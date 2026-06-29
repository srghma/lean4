// Lean compiler output
// Module: Lake.Util.OpaqueType
// Imports: Lake.Util.Binder Init.Prelude
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_Lake_nonemptyTypeCmd___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_nonemptyTypeCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__1_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lake_nonemptyTypeCmd___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_nonemptyTypeCmd___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            2831656807158390110 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_nonemptyTypeCmd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__5_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lake_nonemptyTypeCmd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__7_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lake_nonemptyTypeCmd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__7_value)
                as *mut crate::leanh::LeanObject,
            3961966953292576997 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__11_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [118, 105, 115, 105, 98, 105, 108, 105, 116, 121, 0],
    };
static mut l_Lake_nonemptyTypeCmd___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__11_value)
                as *mut crate::leanh::LeanObject,
            18370519569176055110 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__16_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__19_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lake_nonemptyTypeCmd___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__19_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__23_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lake_nonemptyTypeCmd___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__23_value)
                as *mut crate::leanh::LeanObject,
            2302572775315350313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__25_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_nonemptyTypeCmd___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Lake_nonemptyTypeCmd___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_nonemptyTypeCmd___closed__26_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__25_value)
                as *mut crate::leanh::LeanObject,
            16338829057506708314 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__28_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__27_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__29_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__22_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_nonemptyTypeCmd___closed__30_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__29_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_nonemptyTypeCmd___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__30_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_nonemptyTypeCmd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 115, 116, 78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 105, 112, 101, 80, 114, 111, 106, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [124, 62, 46, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3_value) as *mut crate::leanh::LeanObject,11503787708459150704 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16_value) as *mut crate::leanh::LeanObject,13229434762204987278 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 112, 101, 114, 116, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26_value) as *mut crate::leanh::LeanObject,13877162779417220697 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__30_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__35_value) as *mut crate::leanh::LeanObject,8497769072906204829 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__37_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40_value) as *mut crate::leanh::LeanObject,10324751846086867157 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 112, 97, 113, 117, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__42_value) as *mut crate::leanh::LeanObject,7407402195942431087 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__44_value) as *mut crate::leanh::LeanObject,1827444229220621555 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__46_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48_value) as *mut crate::leanh::LeanObject,5940551064397964566 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__51_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 85, 110, 105, 118, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__54_value) as *mut crate::leanh::LeanObject,4475001683190667726 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56_value) as *mut crate::leanh::LeanObject,1236407310526250327 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__60_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__59_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__61_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 123, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__64_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_hydrateOpaqueTypeCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_hydrateOpaqueTypeCmd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1609764115375978371 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__2_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_hydrateOpaqueTypeCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__24_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_hydrateOpaqueTypeCmd___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_hydrateOpaqueTypeCmd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_hydrateOpaqueTypeCmd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_hydrateOpaqueTypeCmd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,6962862263136859431 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 111, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,16059047048258275031 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__7_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_nonemptyTypeCmd___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut crate::leanh::LeanObject,13340093926952294564 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut crate::leanh::LeanObject,9666231177748665885 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19_value) as *mut crate::leanh::LeanObject,13340093926952294564 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23_value) as *mut crate::leanh::LeanObject,609174137020324014 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 110, 100, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__29_value) as *mut crate::leanh::LeanObject,12500803453736965855 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 110, 115, 97, 102, 101, 77, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,15035602936918917649 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 67, 111, 101, 77, 107, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__35_value) as *mut crate::leanh::LeanObject,6447927339206716348 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [103, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__38_value) as *mut crate::leanh::LeanObject,699949278435066773 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 115, 97, 102, 101, 71, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__41_value) as *mut crate::leanh::LeanObject,15932694652473032876 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 67, 111, 101, 71, 101, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__44_value) as *mut crate::leanh::LeanObject,9226533731144894724 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47_value) as *mut crate::leanh::LeanObject,17575194138276270420 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__49_value) as *mut crate::leanh::LeanObject,2533412339571800130 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__52_value) as *mut crate::leanh::LeanObject,7499624980761693169 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__14_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__55_value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__56_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 108, 105, 110, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58_value) as *mut crate::leanh::LeanObject,8159932143332935260 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__61_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 115, 97, 102, 101, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64_value) as *mut crate::leanh::LeanObject,10398938568477941839 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,9789339221525904376 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__66_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2_value) as *mut crate::leanh::LeanObject,5473625859156281626 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__70_value) as *mut crate::leanh::LeanObject,14917456309791986358 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 146, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5_value) as *mut crate::leanh::LeanObject,13585030837571646948 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 110, 115, 97, 102, 101, 67, 97, 115, 116, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75_value) as *mut crate::leanh::LeanObject,9183409343678294206 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__78_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__11_value) as *mut crate::leanh::LeanObject,7625897890118033792 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__12_value) as *mut crate::leanh::LeanObject,8715860392475343861 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 0]};
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81_value) as *mut crate::leanh::LeanObject,5229394285883816413 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0___closed__0;
    v___x_1277_ = l_Lean_Name_str___override(v_x_1275_, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(
    mut v_x_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1___closed__0;
    v___x_1281_ = l_Lean_Name_str___override(v_x_1279_, v___x_1280_);
    return v___x_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(
    mut v_sz_1282_: usize,
    mut v_i_1283_: usize,
    mut v_bs_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: u8 = 0;
    let mut v_v_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = lean_usize_dec_lt(v_i_1283_, v_sz_1282_);
                if v___x_1285_ == 0 {
                    return v_bs_1284_;
                } else {
                    v_v_1286_ = lean_array_uget(v_bs_1284_, v_i_1283_);
                    v___x_1287_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1293_: *mut crate::leanh::LeanObject,
    mut v_i_1294_: *mut crate::leanh::LeanObject,
    mut v_bs_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1296_: usize = 0;
    let mut v_i_boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1296_ = crate::leanh::lean_unbox_usize(v_sz_1293_);
    crate::leanh::lean_dec(v_sz_1293_);
    v_i_boxed_1297_ = crate::leanh::lean_unbox_usize(v_i_1294_);
    crate::leanh::lean_dec(v_i_1294_);
    v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1295_);
    return v_res_1298_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(
    mut v_sz_1299_: usize,
    mut v_i_1300_: usize,
    mut v_bs_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1302_: u8 = 0;
    let mut v_v_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1302_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
                if v___x_1302_ == 0 {
                    return v_bs_1301_;
                } else {
                    v_v_1303_ = lean_array_uget(v_bs_1301_, v_i_1300_);
                    v___x_1304_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1305_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1304_);
                    crate::leanh::lean_inc(v_v_1303_);
                    v___x_1306_ = l_Lake_BinderSyntaxView_mkBinder(v_v_1303_);
                    v___x_1307_ = l_Lake_BinderSyntaxView_mkArgument(v_v_1303_);
                    v___x_1308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1306_);
                    crate::leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
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
    mut v_sz_1313_: *mut crate::leanh::LeanObject,
    mut v_i_1314_: *mut crate::leanh::LeanObject,
    mut v_bs_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1316_: usize = 0;
    let mut v_i_boxed_1317_: usize = 0;
    let mut v_res_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1316_ = crate::leanh::lean_unbox_usize(v_sz_1313_);
    crate::leanh::lean_dec(v_sz_1313_);
    v_i_boxed_1317_ = crate::leanh::lean_unbox_usize(v_i_1314_);
    crate::leanh::lean_dec(v_i_1314_);
    v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_boxed_1316_, v_i_boxed_1317_, v_bs_1315_);
    return v_res_1318_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3;
    v___x_1329_ = l_String_toRawSubstring_x27(v___x_1328_);
    return v___x_1329_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__16;
    v___x_1339_ = l_String_toRawSubstring_x27(v___x_1338_);
    return v___x_1339_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__26;
    v___x_1352_ = l_String_toRawSubstring_x27(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1375_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__56;
    v___x_1422_ = l_String_toRawSubstring_x27(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: usize = 0;
    let mut v___y_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1616_: u8 = 0;
    let mut v___y_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1653_: usize = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_val_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: usize = 0;
    let mut v___y_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_view_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1721_: usize = 0;
    let mut v___x_1722_: usize = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_view_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_a_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v___y_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1445_ = l_Lake_nonemptyTypeCmd___closed__2;
                crate::leanh::lean_inc(v_x_1442_);
                v___x_1446_ = l_Lean_Syntax_isOfKind(v_x_1442_, v___x_1445_);
                if v___x_1446_ == 0 {
                    crate::leanh::lean_dec(v_x_1442_);
                    v___x_1447_ = crate::leanh::lean_box(1);
                    v___x_1448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
                    crate::leanh::lean_ctor_set(v___x_1448_, 1, v_a_1444_);
                    return v___x_1448_;
                } else {
                    v___x_1449_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1450_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1449_);
                    v___x_1451_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1452_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1451_);
                    v___x_1453_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_id_1454_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1453_);
                    v___x_1712_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1713_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1712_);
                    crate::leanh::lean_dec(v_x_1442_);
                    v_bs_1714_ = l_Lean_Syntax_getArgs(v___x_1713_);
                    crate::leanh::lean_dec(v___x_1713_);
                    v___x_1765_ = l_Lean_Syntax_getOptional_x3f(v___x_1452_);
                    crate::leanh::lean_dec(v___x_1452_);
                    if crate::leanh::lean_obj_tag(v___x_1765_) == 0 {
                        v___x_1766_ = crate::leanh::lean_box(0);
                        v___y_1754_ = v___x_1766_;
                        state = 12;
                        continue;
                    } else {
                        v_val_1767_ = crate::leanh::lean_ctor_get(v___x_1765_, 0);
                        v_isSharedCheck_1774_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1765_)) as u8;
                        if v_isSharedCheck_1774_ == 0 {
                            v___x_1769_ = v___x_1765_;
                            v_isShared_1770_ = v_isSharedCheck_1774_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1767_);
                            crate::leanh::lean_dec(v___x_1765_);
                            v___x_1769_ = crate::leanh::lean_box(0);
                            v_isShared_1770_ = v_isSharedCheck_1774_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1485_ = l_Array_append___redArg(v___y_1458_, v___y_1484_);
                crate::leanh::lean_dec_ref(v___y_1484_);
                crate::leanh::lean_inc_n(v___y_1470_, 5);
                crate::leanh::lean_inc_n(v___y_1475_, 38);
                v___x_1486_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1486_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1486_, 1, v___y_1470_);
                crate::leanh::lean_ctor_set(v___x_1486_, 2, v___x_1485_);
                crate::leanh::lean_inc_ref(v___x_1486_);
                crate::leanh::lean_inc_n(v___y_1472_, 24);
                crate::leanh::lean_inc(v___y_1462_);
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
                crate::leanh::lean_inc_ref_n(v___y_1461_, 4);
                crate::leanh::lean_inc_ref_n(v___y_1457_, 13);
                crate::leanh::lean_inc_ref_n(v___y_1479_, 13);
                v___x_1489_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1488_);
                v___x_1490_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__1;
                v___x_1491_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1491_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
                crate::leanh::lean_inc(v_id_1454_);
                v___x_1492_ = lean_array_push(v___y_1463_, v_id_1454_);
                v___x_1493_ = lean_array_push(v___x_1492_, v___y_1480_);
                crate::leanh::lean_inc_n(v___y_1473_, 2);
                crate::leanh::lean_inc(v___y_1466_);
                v___x_1494_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1494_, 0, v___y_1466_);
                crate::leanh::lean_ctor_set(v___x_1494_, 1, v___y_1473_);
                crate::leanh::lean_ctor_set(v___x_1494_, 2, v___x_1493_);
                v___x_1495_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__2;
                v___x_1496_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1495_);
                v___x_1497_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__3;
                crate::leanh::lean_inc_ref_n(v___y_1464_, 5);
                v___x_1498_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1497_);
                v___x_1499_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__4;
                v___x_1500_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1500_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
                v___x_1501_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1498_, v___x_1500_, v___y_1472_);
                crate::leanh::lean_inc(v___y_1481_);
                crate::leanh::lean_inc(v___y_1478_);
                v___x_1502_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1478_, v___y_1481_, v___x_1501_);
                v___x_1503_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1502_);
                v___x_1504_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___x_1496_, v___y_1471_, v___x_1503_);
                v___x_1505_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__5;
                v___x_1506_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1461_, v___x_1505_);
                v___x_1507_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6;
                v___x_1508_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1508_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
                v___x_1509_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__7;
                v___x_1510_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1509_);
                v___x_1511_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__8;
                v___x_1512_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1512_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1512_, 1, v___x_1511_);
                v___x_1513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__9);
                v___x_1514_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__10;
                crate::leanh::lean_inc_n(v___y_1459_, 2);
                crate::leanh::lean_inc_n(v___y_1469_, 2);
                v___x_1515_ = l_Lean_addMacroScope(v___y_1469_, v___x_1514_, v___y_1459_);
                crate::leanh::lean_inc_n(v___y_1477_, 3);
                v___x_1516_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1516_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1516_, 1, v___x_1513_);
                crate::leanh::lean_ctor_set(v___x_1516_, 2, v___x_1515_);
                crate::leanh::lean_ctor_set(v___x_1516_, 3, v___y_1477_);
                crate::leanh::lean_inc_ref(v___x_1512_);
                crate::leanh::lean_inc(v___y_1465_);
                crate::leanh::lean_inc(v___x_1510_);
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
                crate::leanh::lean_inc(v___x_1521_);
                crate::leanh::lean_inc_ref(v___x_1508_);
                crate::leanh::lean_inc(v___x_1506_);
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
                crate::leanh::lean_inc(v___y_1476_);
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
                v___x_1531_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1531_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1526_);
                v___x_1532_ =
                    l_Lean_Syntax_node2(v___y_1475_, v___y_1473_, v___y_1467_, v___y_1472_);
                v___x_1533_ = l_Lean_Syntax_node1(v___y_1475_, v___y_1470_, v___x_1532_);
                v___x_1534_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__15;
                v___x_1535_ =
                    l_Lean_Name_mkStr4(v___y_1479_, v___y_1457_, v___y_1464_, v___x_1534_);
                v___x_1536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__17);
                v___x_1537_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__18;
                v___x_1538_ = l_Lean_addMacroScope(v___y_1469_, v___x_1537_, v___y_1459_);
                crate::leanh::lean_inc(v___y_1460_);
                v___x_1539_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1537_);
                crate::leanh::lean_ctor_set(v___x_1539_, 1, v___y_1460_);
                v___x_1540_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__19;
                v___x_1541_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1540_);
                crate::leanh::lean_ctor_set(v___x_1541_, 1, v___y_1477_);
                v___x_1542_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                v___x_1543_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1543_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1543_, 1, v___x_1536_);
                crate::leanh::lean_ctor_set(v___x_1543_, 2, v___x_1538_);
                crate::leanh::lean_ctor_set(v___x_1543_, 3, v___x_1542_);
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
                v___x_1552_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1552_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1552_, 1, v___x_1551_);
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
                v___x_1560_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1560_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1560_, 1, v___x_1558_);
                v___x_1561_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__27);
                v___x_1562_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__28;
                v___x_1563_ = l_Lean_addMacroScope(v___y_1469_, v___x_1562_, v___y_1459_);
                v___x_1564_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1564_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1564_, 1, v___x_1561_);
                crate::leanh::lean_ctor_set(v___x_1564_, 2, v___x_1563_);
                crate::leanh::lean_ctor_set(v___x_1564_, 3, v___y_1477_);
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
                v___x_1575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                crate::leanh::lean_ctor_set(v___x_1575_, 1, v___y_1468_);
                return v___x_1575_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_1580_);
                v___x_1606_ = l_Array_append___redArg(v___y_1580_, v___y_1605_);
                crate::leanh::lean_dec_ref(v___y_1605_);
                crate::leanh::lean_inc(v___y_1591_);
                crate::leanh::lean_inc(v___y_1596_);
                v___x_1607_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1607_, 0, v___y_1596_);
                crate::leanh::lean_ctor_set(v___x_1607_, 1, v___y_1591_);
                crate::leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
                if crate::leanh::lean_obj_tag(v___y_1601_) == 1 {
                    v_val_1608_ = crate::leanh::lean_ctor_get(v___y_1601_, 0);
                    crate::leanh::lean_inc(v_val_1608_);
                    crate::leanh::lean_dec_ref_known(v___y_1601_, 1);
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
                    crate::leanh::lean_dec(v___y_1601_);
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
                v_quotContext_1621_ = crate::leanh::lean_ctor_get(v_a_1443_, 1);
                v_currMacroScope_1622_ = crate::leanh::lean_ctor_get(v_a_1443_, 2);
                v_ref_1623_ = crate::leanh::lean_ctor_get(v_a_1443_, 5);
                v___x_1624_ = l_Lean_mkIdentFrom(v_id_1454_, v___y_1620_, v___y_1616_);
                crate::leanh::lean_inc_ref(v___y_1619_);
                crate::leanh::lean_inc(v___y_1615_);
                v___x_1625_ = l_Lean_Syntax_mkApp(v___y_1615_, v___y_1619_);
                v___x_1626_ = l_Lean_SourceInfo_fromRef(v_ref_1623_, v___y_1616_);
                v___x_1627_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                v___x_1628_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32;
                v___x_1629_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33;
                v___x_1630_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34;
                v___x_1631_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36;
                v___x_1632_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38;
                v___x_1633_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
                crate::leanh::lean_inc_n(v___x_1626_, 19);
                v___x_1634_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1627_);
                crate::leanh::lean_ctor_set(v___x_1634_, 2, v___x_1633_);
                v___x_1635_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__40;
                v___x_1636_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__41;
                v___x_1637_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1637_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1637_, 1, v___x_1635_);
                v___x_1638_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1636_, v___x_1637_);
                v___x_1639_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1627_, v___x_1638_);
                crate::leanh::lean_inc_ref_n(v___x_1634_, 7);
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
                v___x_1643_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1643_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1643_, 1, v___x_1641_);
                v___x_1644_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
                v___x_1645_ = crate::leanh::lean_box(2);
                v___x_1646_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
                v___x_1647_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
                crate::leanh::lean_inc_ref(v___x_1648_);
                v___x_1649_ = lean_array_push(v___x_1648_, v___y_1615_);
                v___x_1650_ = lean_array_push(v___x_1649_, v___x_1646_);
                v___x_1651_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1645_);
                crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1644_);
                crate::leanh::lean_ctor_set(v___x_1651_, 2, v___x_1650_);
                v___x_1652_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__49;
                v_sz_1653_ = lean_array_size(v___y_1612_);
                v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__1(v_sz_1653_, v___y_1614_, v___y_1612_);
                v___x_1655_ = l_Array_append___redArg(v___x_1633_, v___x_1654_);
                crate::leanh::lean_dec_ref(v___x_1654_);
                v___x_1656_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1627_);
                crate::leanh::lean_ctor_set(v___x_1656_, 2, v___x_1655_);
                v___x_1657_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50;
                v___x_1658_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52;
                v___x_1659_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53;
                v___x_1660_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                v___x_1661_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__55;
                v___x_1662_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__57);
                v___x_1663_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__58;
                crate::leanh::lean_inc(v_currMacroScope_1622_);
                crate::leanh::lean_inc(v_quotContext_1621_);
                v___x_1664_ =
                    l_Lean_addMacroScope(v_quotContext_1621_, v___x_1663_, v_currMacroScope_1622_);
                v___x_1665_ = crate::leanh::lean_box(0);
                v___x_1666_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__62;
                v___x_1667_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1667_, 1, v___x_1662_);
                crate::leanh::lean_ctor_set(v___x_1667_, 2, v___x_1664_);
                crate::leanh::lean_ctor_set(v___x_1667_, 3, v___x_1666_);
                v___x_1668_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__63;
                v___x_1669_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1669_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1669_, 1, v___x_1668_);
                v___x_1670_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__65;
                v___x_1671_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__66;
                v___x_1672_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1670_, v___x_1672_);
                v___x_1674_ = l_Lean_Syntax_node1(v___x_1626_, v___x_1627_, v___x_1673_);
                v___x_1675_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67;
                v___x_1676_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1676_, 0, v___x_1626_);
                crate::leanh::lean_ctor_set(v___x_1676_, 1, v___x_1675_);
                v___x_1677_ = l_Lean_Syntax_node4(
                    v___x_1626_,
                    v___x_1661_,
                    v___x_1667_,
                    v___x_1669_,
                    v___x_1674_,
                    v___x_1676_,
                );
                crate::leanh::lean_inc_ref(v___x_1660_);
                v___x_1678_ =
                    l_Lean_Syntax_node2(v___x_1626_, v___x_1658_, v___x_1660_, v___x_1677_);
                crate::leanh::lean_inc_ref(v___x_1656_);
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
                if crate::leanh::lean_obj_tag(v___y_1617_) == 1 {
                    v_val_1682_ = crate::leanh::lean_ctor_get(v___y_1617_, 0);
                    crate::leanh::lean_inc(v_val_1682_);
                    crate::leanh::lean_dec_ref_known(v___y_1617_, 1);
                    v___x_1683_ = l_Array_mkArray1___redArg(v_val_1682_);
                    crate::leanh::lean_inc(v_quotContext_1621_);
                    crate::leanh::lean_inc(v_currMacroScope_1622_);
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
                    crate::leanh::lean_dec(v___y_1617_);
                    v___x_1684_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29;
                    crate::leanh::lean_inc(v_quotContext_1621_);
                    crate::leanh::lean_inc(v_currMacroScope_1622_);
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
                    v_name_1699_ = crate::leanh::lean_ctor_get(v_view_1698_, 0);
                    v_imported_1700_ = crate::leanh::lean_ctor_get(v_view_1698_, 1);
                    v_ctx_1701_ = crate::leanh::lean_ctor_get(v_view_1698_, 2);
                    v_scopes_1702_ = crate::leanh::lean_ctor_get(v_view_1698_, 3);
                    v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v_view_1698_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1704_ = v_view_1698_;
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_scopes_1702_);
                        crate::leanh::lean_inc(v_ctx_1701_);
                        crate::leanh::lean_inc(v_imported_1700_);
                        crate::leanh::lean_inc(v_name_1699_);
                        crate::leanh::lean_dec(v_view_1698_);
                        v___x_1704_ = crate::leanh::lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1706_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__1(v_name_1699_);
                if v_isShared_1705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1706_);
                    v___x_1708_ = v___x_1704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_imported_1700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_ctx_1701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_scopes_1702_);
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
                crate::leanh::lean_dec_ref(v_bs_1714_);
                if crate::leanh::lean_obj_tag(v___x_1718_) == 0 {
                    v_a_1719_ = crate::leanh::lean_ctor_get(v___x_1718_, 0);
                    crate::leanh::lean_inc(v_a_1719_);
                    v_a_1720_ = crate::leanh::lean_ctor_get(v___x_1718_, 1);
                    crate::leanh::lean_inc(v_a_1720_);
                    crate::leanh::lean_dec_ref_known(v___x_1718_, 2);
                    v_sz_1721_ = lean_array_size(v_a_1719_);
                    v___x_1722_ = 0usize;
                    v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1_spec__0(v_sz_1721_, v___x_1722_, v_a_1719_);
                    v___x_1724_ = l_Array_unzip___redArg(v___x_1723_);
                    crate::leanh::lean_dec_ref(v___x_1723_);
                    v_fst_1725_ = crate::leanh::lean_ctor_get(v___x_1724_, 0);
                    crate::leanh::lean_inc(v_fst_1725_);
                    v_snd_1726_ = crate::leanh::lean_ctor_get(v___x_1724_, 1);
                    crate::leanh::lean_inc(v_snd_1726_);
                    crate::leanh::lean_dec_ref(v___x_1724_);
                    v___x_1727_ = l_Lean_TSyntax_getId(v_id_1454_);
                    v___x_1728_ = l_Lean_Name_hasMacroScopes(v___x_1727_);
                    if v___x_1728_ == 0 {
                        crate::leanh::lean_inc(v___x_1727_);
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
                        crate::leanh::lean_inc(v___x_1727_);
                        v_view_1730_ = l_Lean_extractMacroScopes(v___x_1727_);
                        v_name_1731_ = crate::leanh::lean_ctor_get(v_view_1730_, 0);
                        v_imported_1732_ = crate::leanh::lean_ctor_get(v_view_1730_, 1);
                        v_ctx_1733_ = crate::leanh::lean_ctor_get(v_view_1730_, 2);
                        v_scopes_1734_ = crate::leanh::lean_ctor_get(v_view_1730_, 3);
                        v_isSharedCheck_1743_ =
                            (!crate::leanh::lean_is_exclusive(v_view_1730_)) as u8;
                        if v_isSharedCheck_1743_ == 0 {
                            v___x_1736_ = v_view_1730_;
                            v_isShared_1737_ = v_isSharedCheck_1743_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_scopes_1734_);
                            crate::leanh::lean_inc(v_ctx_1733_);
                            crate::leanh::lean_inc(v_imported_1732_);
                            crate::leanh::lean_inc(v_name_1731_);
                            crate::leanh::lean_dec(v_view_1730_);
                            v___x_1736_ = crate::leanh::lean_box(0);
                            v_isShared_1737_ = v_isSharedCheck_1743_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1717_);
                    crate::leanh::lean_dec(v___y_1716_);
                    crate::leanh::lean_dec(v_id_1454_);
                    v_a_1744_ = crate::leanh::lean_ctor_get(v___x_1718_, 0);
                    v_a_1745_ = crate::leanh::lean_ctor_get(v___x_1718_, 1);
                    v_isSharedCheck_1752_ = (!crate::leanh::lean_is_exclusive(v___x_1718_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1747_ = v___x_1718_;
                        v_isShared_1748_ = v_isSharedCheck_1752_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1745_);
                        crate::leanh::lean_inc(v_a_1744_);
                        crate::leanh::lean_dec(v___x_1718_);
                        v___x_1747_ = crate::leanh::lean_box(0);
                        v_isShared_1748_ = v_isSharedCheck_1752_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1738_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___lam__0(v_name_1731_);
                if v_isShared_1737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1736_, 0, v___x_1738_);
                    v___x_1740_ = v___x_1736_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_imported_1732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_ctx_1733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_scopes_1734_);
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
                    v_reuseFailAlloc_1751_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1745_);
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
                crate::leanh::lean_dec(v___x_1450_);
                if crate::leanh::lean_obj_tag(v___x_1755_) == 0 {
                    v___x_1756_ = crate::leanh::lean_box(0);
                    v___y_1716_ = v___y_1754_;
                    v___y_1717_ = v___x_1756_;
                    state = 7;
                    continue;
                } else {
                    v_val_1757_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                    v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                    if v_isSharedCheck_1764_ == 0 {
                        v___x_1759_ = v___x_1755_;
                        v_isShared_1760_ = v_isSharedCheck_1764_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1757_);
                        crate::leanh::lean_dec(v___x_1755_);
                        v___x_1759_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_val_1757_);
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
                    v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_val_1767_);
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
    mut v_x_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1(
        v_x_1775_, v_a_1776_, v_a_1777_,
    );
    crate::leanh::lean_dec_ref(v_a_1776_);
    return v_res_1778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(
    mut v_sz_1810_: usize,
    mut v_i_1811_: usize,
    mut v_bs_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: u8 = 0;
    let mut v_v_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1813_ = lean_usize_dec_lt(v_i_1811_, v_sz_1810_);
                if v___x_1813_ == 0 {
                    return v_bs_1812_;
                } else {
                    v_v_1814_ = lean_array_uget(v_bs_1812_, v_i_1811_);
                    v___x_1815_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1821_: *mut crate::leanh::LeanObject,
    mut v_i_1822_: *mut crate::leanh::LeanObject,
    mut v_bs_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1824_: usize = 0;
    let mut v_i_boxed_1825_: usize = 0;
    let mut v_res_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1824_ = crate::leanh::lean_unbox_usize(v_sz_1821_);
    crate::leanh::lean_dec(v_sz_1821_);
    v_i_boxed_1825_ = crate::leanh::lean_unbox_usize(v_i_1822_);
    crate::leanh::lean_dec(v_i_1822_);
    v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1823_);
    return v_res_1826_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(
    mut v_sz_1827_: usize,
    mut v_i_1828_: usize,
    mut v_bs_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: u8 = 0;
    let mut v_v_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1830_ = lean_usize_dec_lt(v_i_1828_, v_sz_1827_);
                if v___x_1830_ == 0 {
                    return v_bs_1829_;
                } else {
                    v_v_1831_ = lean_array_uget(v_bs_1829_, v_i_1828_);
                    v___x_1832_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1838_: *mut crate::leanh::LeanObject,
    mut v_i_1839_: *mut crate::leanh::LeanObject,
    mut v_bs_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1841_: usize = 0;
    let mut v_i_boxed_1842_: usize = 0;
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1841_ = crate::leanh::lean_unbox_usize(v_sz_1838_);
    crate::leanh::lean_dec(v_sz_1838_);
    v_i_boxed_1842_ = crate::leanh::lean_unbox_usize(v_i_1839_);
    crate::leanh::lean_dec(v_i_1839_);
    v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v_sz_boxed_1841_, v_i_boxed_1842_, v_bs_1840_);
    return v_res_1843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(
    mut v___x_1851_: *mut crate::leanh::LeanObject,
    mut v___x_1852_: *mut crate::leanh::LeanObject,
    mut v_sz_1853_: usize,
    mut v_i_1854_: usize,
    mut v_bs_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1856_ = lean_usize_dec_lt(v_i_1854_, v_sz_1853_);
                if v___x_1856_ == 0 {
                    crate::leanh::lean_dec(v___x_1852_);
                    crate::leanh::lean_dec(v___x_1851_);
                    return v_bs_1855_;
                } else {
                    v___x_1857_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                    v_v_1858_ = lean_array_uget(v_bs_1855_, v_i_1854_);
                    v___x_1859_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1860_ = lean_array_uset(v_bs_1855_, v_i_1854_, v___x_1859_);
                    v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__1;
                    v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2___closed__2;
                    crate::leanh::lean_inc_n(v___x_1851_, 4);
                    v___x_1863_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1851_);
                    crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                    v___x_1864_ = l_Lean_Syntax_node1(v___x_1851_, v___x_1857_, v_v_1858_);
                    v___x_1865_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__67;
                    v___x_1866_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1851_);
                    crate::leanh::lean_ctor_set(v___x_1866_, 1, v___x_1865_);
                    crate::leanh::lean_inc(v___x_1852_);
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
    mut v___x_1872_: *mut crate::leanh::LeanObject,
    mut v___x_1873_: *mut crate::leanh::LeanObject,
    mut v_sz_1874_: *mut crate::leanh::LeanObject,
    mut v_i_1875_: *mut crate::leanh::LeanObject,
    mut v_bs_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1877_: usize = 0;
    let mut v_i_boxed_1878_: usize = 0;
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1877_ = crate::leanh::lean_unbox_usize(v_sz_1874_);
    crate::leanh::lean_dec(v_sz_1874_);
    v_i_boxed_1878_ = crate::leanh::lean_unbox_usize(v_i_1875_);
    crate::leanh::lean_dec(v_i_1875_);
    v_res_1879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___x_1872_, v___x_1873_, v_sz_boxed_1877_, v_i_boxed_1878_, v_bs_1876_);
    return v_res_1879_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__0;
    v___x_1882_ = l_String_toRawSubstring_x27(v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__9;
    v___x_1895_ = l_String_toRawSubstring_x27(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__19;
    v___x_1908_ = l_String_toRawSubstring_x27(v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__23;
    v___x_1915_ = l_String_toRawSubstring_x27(v___x_1914_);
    return v___x_1915_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mk_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__30;
    v_mk_1928_ = lean_mk_syntax_ident(v___x_1927_);
    return v_mk_1928_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__33;
    v_unsafeMk_1933_ = lean_mk_syntax_ident(v___x_1932_);
    return v_unsafeMk_1933_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeMk_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__36;
    v_instCoeMk_1938_ = lean_mk_syntax_ident(v___x_1937_);
    return v_instCoeMk_1938_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__39;
    v_get_1943_ = lean_mk_syntax_ident(v___x_1942_);
    return v_get_1943_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeGet_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1947_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__42;
    v_unsafeGet_1948_ = lean_mk_syntax_ident(v___x_1947_);
    return v_unsafeGet_1948_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeGet_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__45;
    v_instCoeGet_1953_ = lean_mk_syntax_ident(v___x_1952_);
    return v_instCoeGet_1953_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__58;
    v___x_1987_ = l_String_toRawSubstring_x27(v___x_1986_);
    return v___x_1987_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
    v_unsafeMk_2009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
    v___x_2010_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2011_ = lean_mk_empty_array_with_capacity(v___x_2010_);
    v___x_2012_ = lean_array_push(v___x_2011_, v_unsafeMk_2009_);
    v___x_2013_ = lean_array_push(v___x_2012_, v___x_2008_);
    return v___x_2013_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__67);
    v___x_2015_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
    v___x_2016_ = crate::leanh::lean_box(2);
    v___x_2017_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2016_);
    crate::leanh::lean_ctor_set(v___x_2017_, 1, v___x_2015_);
    crate::leanh::lean_ctor_set(v___x_2017_, 2, v___x_2014_);
    return v___x_2017_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__75;
    v___x_2042_ = l_String_toRawSubstring_x27(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__81;
    v___x_2058_ = l_String_toRawSubstring_x27(v___x_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(
    mut v_x_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: usize = 0;
    let mut v___y_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___y_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: usize = 0;
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2215_: usize = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mk_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeMk_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeMk_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unsafeGet_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instCoeGet_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2358_: usize = 0;
    let mut v___x_2359_: usize = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2064_ = l_Lake_hydrateOpaqueTypeCmd___closed__1;
                crate::leanh::lean_inc(v_x_2061_);
                v___x_2065_ = l_Lean_Syntax_isOfKind(v_x_2061_, v___x_2064_);
                if v___x_2065_ == 0 {
                    crate::leanh::lean_dec(v_x_2061_);
                    v___x_2066_ = crate::leanh::lean_box(1);
                    v___x_2067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2067_, 0, v___x_2066_);
                    crate::leanh::lean_ctor_set(v___x_2067_, 1, v_a_2063_);
                    return v___x_2067_;
                } else {
                    v___x_2068_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2069_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2068_);
                    v___x_2070_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2071_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2070_);
                    v___x_2072_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2073_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2072_);
                    v___x_2074_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2075_ = l_Lean_Syntax_getArg(v_x_2061_, v___x_2074_);
                    crate::leanh::lean_dec(v_x_2061_);
                    v_args_2076_ = l_Lean_Syntax_getArgs(v___x_2075_);
                    crate::leanh::lean_dec(v___x_2075_);
                    v___x_2397_ = l_Lean_Syntax_getOptional_x3f(v___x_2069_);
                    crate::leanh::lean_dec(v___x_2069_);
                    if crate::leanh::lean_obj_tag(v___x_2397_) == 0 {
                        v___x_2398_ = crate::leanh::lean_box(0);
                        v___y_2288_ = v___x_2398_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2399_ = crate::leanh::lean_ctor_get(v___x_2397_, 0);
                        v_isSharedCheck_2406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2397_)) as u8;
                        if v_isSharedCheck_2406_ == 0 {
                            v___x_2401_ = v___x_2397_;
                            v_isShared_2402_ = v_isSharedCheck_2406_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2399_);
                            crate::leanh::lean_dec(v___x_2397_);
                            v___x_2401_ = crate::leanh::lean_box(0);
                            v_isShared_2402_ = v_isSharedCheck_2406_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2084_);
                v___x_2130_ = l_Array_append___redArg(v___y_2084_, v___y_2129_);
                crate::leanh::lean_dec_ref(v___y_2129_);
                crate::leanh::lean_inc_n(v___y_2122_, 18);
                crate::leanh::lean_inc_n(v___y_2119_, 79);
                v___x_2131_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2131_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2131_, 1, v___y_2122_);
                crate::leanh::lean_ctor_set(v___x_2131_, 2, v___x_2130_);
                crate::leanh::lean_inc_ref_n(v___x_2131_, 2);
                crate::leanh::lean_inc_n(v___y_2086_, 34);
                crate::leanh::lean_inc_n(v___y_2118_, 2);
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
                crate::leanh::lean_inc_ref_n(v___y_2106_, 4);
                crate::leanh::lean_inc_ref_n(v___y_2125_, 8);
                crate::leanh::lean_inc_ref_n(v___y_2089_, 9);
                v___x_2134_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2133_);
                v___x_2135_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2133_);
                crate::leanh::lean_inc_n(v___y_2079_, 3);
                crate::leanh::lean_inc_ref_n(v___y_2082_, 2);
                v___x_2136_ = lean_array_push(v___y_2082_, v___y_2079_);
                crate::leanh::lean_inc_n(v___y_2096_, 3);
                v___x_2137_ = lean_array_push(v___x_2136_, v___y_2096_);
                crate::leanh::lean_inc_n(v___y_2094_, 5);
                crate::leanh::lean_inc_n(v___y_2110_, 3);
                v___x_2138_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2138_, 0, v___y_2110_);
                crate::leanh::lean_ctor_set(v___x_2138_, 1, v___y_2094_);
                crate::leanh::lean_ctor_set(v___x_2138_, 2, v___x_2137_);
                v___x_2139_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__48;
                v___x_2140_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2106_, v___x_2139_);
                crate::leanh::lean_inc_n(v___x_2140_, 4);
                v___x_2141_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___y_2086_, v___y_2095_);
                crate::leanh::lean_inc_ref(v___x_2135_);
                crate::leanh::lean_inc(v___x_2134_);
                v___x_2142_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___x_2134_,
                    v___x_2135_,
                    v___x_2138_,
                    v___x_2141_,
                    v___y_2086_,
                );
                crate::leanh::lean_inc_n(v___y_2126_, 5);
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
                v___x_2147_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2147_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2145_);
                crate::leanh::lean_inc(v___y_2083_);
                v___x_2148_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2094_, v___y_2083_, v___y_2086_);
                v___x_2149_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2148_);
                v___x_2150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__1);
                v___x_2151_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__2;
                crate::leanh::lean_inc_n(v___y_2092_, 3);
                crate::leanh::lean_inc_n(v___y_2105_, 3);
                v___x_2152_ = l_Lean_addMacroScope(v___y_2105_, v___x_2151_, v___y_2092_);
                crate::leanh::lean_inc_n(v___y_2116_, 3);
                v___x_2153_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2151_);
                crate::leanh::lean_ctor_set(v___x_2153_, 1, v___y_2116_);
                v___x_2154_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__3;
                crate::leanh::lean_inc_n(v___y_2117_, 4);
                v___x_2155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                crate::leanh::lean_ctor_set(v___x_2155_, 1, v___y_2117_);
                v___x_2156_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2156_, 0, v___x_2153_);
                crate::leanh::lean_ctor_set(v___x_2156_, 1, v___x_2155_);
                v___x_2157_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2157_, 1, v___x_2150_);
                crate::leanh::lean_ctor_set(v___x_2157_, 2, v___x_2152_);
                crate::leanh::lean_ctor_set(v___x_2157_, 3, v___x_2156_);
                v___x_2158_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__4;
                crate::leanh::lean_inc_ref_n(v___y_2111_, 4);
                v___x_2159_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2158_);
                v___x_2160_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__5;
                v___x_2161_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2160_);
                v___x_2162_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__6;
                v___x_2163_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2163_, 1, v___x_2162_);
                v___x_2164_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__8;
                v___x_2165_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__10);
                v___x_2166_ = crate::leanh::lean_box(0);
                v___x_2167_ = l_Lean_addMacroScope(v___y_2105_, v___x_2166_, v___y_2092_);
                v___x_2168_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__12;
                v___x_2169_ = l_Lean_Name_mkStr1(v___y_2089_);
                v___x_2170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2169_);
                v___x_2171_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                crate::leanh::lean_ctor_set(v___x_2171_, 1, v___y_2117_);
                v___x_2172_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2172_, 0, v___x_2168_);
                crate::leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
                v___x_2173_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2173_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2173_, 1, v___x_2165_);
                crate::leanh::lean_ctor_set(v___x_2173_, 2, v___x_2167_);
                crate::leanh::lean_ctor_set(v___x_2173_, 3, v___x_2172_);
                v___x_2174_ = l_Lean_Syntax_node1(v___y_2119_, v___x_2164_, v___x_2173_);
                v___x_2175_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2161_, v___x_2163_, v___x_2174_);
                v___x_2176_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__13;
                v___x_2177_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2177_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2177_, 1, v___x_2176_);
                crate::leanh::lean_inc_ref(v___x_2177_);
                crate::leanh::lean_inc(v___y_2099_);
                crate::leanh::lean_inc(v___x_2175_);
                crate::leanh::lean_inc(v___x_2159_);
                v___x_2178_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2159_,
                    v___x_2175_,
                    v___y_2099_,
                    v___x_2177_,
                );
                crate::leanh::lean_inc(v___y_2102_);
                v___x_2179_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2159_,
                    v___x_2175_,
                    v___y_2102_,
                    v___x_2177_,
                );
                crate::leanh::lean_inc_n(v___x_2179_, 2);
                crate::leanh::lean_inc_n(v___x_2178_, 2);
                v___x_2180_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2122_, v___x_2178_, v___x_2179_);
                crate::leanh::lean_inc_ref(v___x_2157_);
                crate::leanh::lean_inc_n(v___y_2104_, 4);
                v___x_2181_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2104_, v___x_2157_, v___x_2180_);
                crate::leanh::lean_inc_n(v___y_2107_, 3);
                crate::leanh::lean_inc_n(v___y_2101_, 3);
                v___x_2182_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2181_);
                v___x_2183_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2140_, v___y_2086_, v___x_2182_);
                v___x_2184_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__14;
                v___x_2185_ =
                    l_Lean_Name_mkStr4(v___y_2089_, v___y_2125_, v___y_2111_, v___x_2184_);
                v___x_2186_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__15;
                v___x_2187_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2187_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
                v___x_2188_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___y_2079_);
                v___x_2189_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__16;
                v___x_2190_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2190_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2190_, 1, v___x_2189_);
                crate::leanh::lean_inc_ref_n(v___x_2190_, 2);
                crate::leanh::lean_inc_ref_n(v___x_2187_, 2);
                crate::leanh::lean_inc_n(v___x_2185_, 2);
                v___x_2191_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___x_2185_,
                    v___x_2187_,
                    v___x_2188_,
                    v___x_2190_,
                );
                crate::leanh::lean_inc_n(v___y_2114_, 2);
                crate::leanh::lean_inc_n(v___y_2093_, 2);
                crate::leanh::lean_inc_n(v___y_2123_, 2);
                v___x_2192_ = l_Lean_Syntax_node4(
                    v___y_2119_,
                    v___y_2123_,
                    v___y_2093_,
                    v___x_2191_,
                    v___y_2114_,
                    v___y_2086_,
                );
                crate::leanh::lean_inc_ref_n(v___x_2147_, 2);
                crate::leanh::lean_inc_n(v___y_2127_, 3);
                crate::leanh::lean_inc_n(v___x_2146_, 2);
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
                crate::leanh::lean_inc_n(v___x_2144_, 2);
                v___x_2194_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2126_, v___x_2144_, v___x_2193_);
                crate::leanh::lean_inc_n(v___y_2124_, 2);
                v___x_2195_ = lean_array_push(v___y_2082_, v___y_2124_);
                v___x_2196_ = lean_array_push(v___x_2195_, v___y_2096_);
                v___x_2197_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2197_, 0, v___y_2110_);
                crate::leanh::lean_ctor_set(v___x_2197_, 1, v___y_2094_);
                crate::leanh::lean_ctor_set(v___x_2197_, 2, v___x_2196_);
                v___x_2198_ = l_Lean_Syntax_node3(
                    v___y_2119_,
                    v___y_2080_,
                    v___y_2102_,
                    v___y_2128_,
                    v___y_2099_,
                );
                v___x_2199_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2101_, v___y_2107_, v___x_2198_);
                crate::leanh::lean_inc(v___x_2199_);
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
                crate::leanh::lean_inc(v___y_2109_);
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
                crate::leanh::lean_inc_n(v___y_2113_, 2);
                v___x_2211_ = lean_array_push(v___y_2082_, v___y_2113_);
                v___x_2212_ = lean_array_push(v___x_2211_, v___y_2096_);
                v___x_2213_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2213_, 0, v___y_2110_);
                crate::leanh::lean_ctor_set(v___x_2213_, 1, v___y_2094_);
                crate::leanh::lean_ctor_set(v___x_2213_, 2, v___x_2212_);
                v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__1(v___y_2078_, v___y_2121_, v_args_2076_);
                v_sz_2215_ = lean_array_size(v___x_2214_);
                v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__2(v___y_2119_, v___y_2086_, v_sz_2215_, v___y_2121_, v___x_2214_);
                v___x_2217_ = l_Array_append___redArg(v___y_2084_, v___x_2216_);
                crate::leanh::lean_dec_ref(v___x_2216_);
                v___x_2218_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2218_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2218_, 1, v___y_2122_);
                crate::leanh::lean_ctor_set(v___x_2218_, 2, v___x_2217_);
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
                crate::leanh::lean_inc(v___y_2100_);
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
                v___x_2236_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2236_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2236_, 1, v___x_2235_);
                v___x_2237_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__20);
                v___x_2238_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__21;
                v___x_2239_ = l_Lean_addMacroScope(v___y_2105_, v___x_2238_, v___y_2092_);
                v___x_2240_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2238_);
                crate::leanh::lean_ctor_set(v___x_2240_, 1, v___y_2116_);
                v___x_2241_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__22;
                v___x_2242_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2242_, 0, v___x_2241_);
                crate::leanh::lean_ctor_set(v___x_2242_, 1, v___y_2117_);
                v___x_2243_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2240_);
                crate::leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
                v___x_2244_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2244_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2244_, 1, v___x_2237_);
                crate::leanh::lean_ctor_set(v___x_2244_, 2, v___x_2239_);
                crate::leanh::lean_ctor_set(v___x_2244_, 3, v___x_2243_);
                v___x_2245_ = l_Lean_Syntax_node1(v___y_2119_, v___y_2122_, v___x_2178_);
                crate::leanh::lean_inc_ref(v___x_2244_);
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
                v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__24);
                v___x_2254_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__25;
                v___x_2255_ = l_Lean_addMacroScope(v___y_2105_, v___x_2254_, v___y_2092_);
                v___x_2256_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__26;
                v___x_2257_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2256_);
                crate::leanh::lean_ctor_set(v___x_2257_, 1, v___y_2116_);
                v___x_2258_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__27;
                v___x_2259_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
                crate::leanh::lean_ctor_set(v___x_2259_, 1, v___y_2117_);
                v___x_2260_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2260_, 0, v___x_2257_);
                crate::leanh::lean_ctor_set(v___x_2260_, 1, v___x_2259_);
                v___x_2261_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2261_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2253_);
                crate::leanh::lean_ctor_set(v___x_2261_, 2, v___x_2255_);
                crate::leanh::lean_ctor_set(v___x_2261_, 3, v___x_2260_);
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
                v___x_2271_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2271_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2271_, 1, v___x_2269_);
                v___x_2272_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___y_2122_, v___x_2071_, v___y_2086_);
                v___x_2273_ =
                    l_Lean_Syntax_node2(v___y_2119_, v___x_2270_, v___x_2271_, v___x_2272_);
                v___x_2274_ = crate::leanh::lean_unsigned_to_nat(9);
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
                v___x_2285_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2285_, 0, v___y_2119_);
                crate::leanh::lean_ctor_set(v___x_2285_, 1, v___y_2122_);
                crate::leanh::lean_ctor_set(v___x_2285_, 2, v___x_2284_);
                v___x_2286_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2285_);
                crate::leanh::lean_ctor_set(v___x_2286_, 1, v_a_2063_);
                return v___x_2286_;
            }
            2 => {
                v_quotContext_2289_ = crate::leanh::lean_ctor_get(v_a_2062_, 1);
                v_currMacroScope_2290_ = crate::leanh::lean_ctor_get(v_a_2062_, 2);
                v_ref_2291_ = crate::leanh::lean_ctor_get(v_a_2062_, 5);
                v_mk_2292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__31);
                v_unsafeMk_2293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__34);
                v_instCoeMk_2294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__37);
                v_get_2295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__40);
                v_unsafeGet_2296_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__43);
                v_instCoeGet_2297_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__46);
                v___x_2298_ = 0;
                v___x_2299_ = l_Lean_SourceInfo_fromRef(v_ref_2291_, v___x_2298_);
                v___x_2300_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__31;
                v___x_2301_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__32;
                v___x_2302_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__33;
                v___x_2303_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__34;
                v___x_2304_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__47;
                v___x_2305_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__48;
                crate::leanh::lean_inc_n(v___x_2299_, 42);
                v___x_2306_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2306_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2306_, 1, v___x_2304_);
                crate::leanh::lean_inc_n(v___x_2071_, 2);
                v___x_2307_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2305_, v___x_2306_, v___x_2071_);
                v___x_2308_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__36;
                v___x_2309_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__38;
                v___x_2310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__39);
                v___x_2311_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2311_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2311_, 1, v___x_2300_);
                crate::leanh::lean_ctor_set(v___x_2311_, 2, v___x_2310_);
                v___x_2312_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__50;
                v___x_2313_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__50;
                v___x_2314_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__51;
                v___x_2315_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                v___x_2316_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__53;
                v___x_2317_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__54;
                crate::leanh::lean_inc_ref_n(v___x_2311_, 11);
                v___x_2318_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2317_, v___x_2311_);
                v___x_2319_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__57;
                v___x_2320_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__59);
                v___x_2321_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__60;
                crate::leanh::lean_inc_n(v_currMacroScope_2290_, 3);
                crate::leanh::lean_inc_n(v_quotContext_2289_, 3);
                v___x_2322_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2321_, v_currMacroScope_2290_);
                v___x_2323_ = crate::leanh::lean_box(0);
                v___x_2324_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__62;
                v___x_2325_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2325_, 1, v___x_2320_);
                crate::leanh::lean_ctor_set(v___x_2325_, 2, v___x_2322_);
                crate::leanh::lean_ctor_set(v___x_2325_, 3, v___x_2324_);
                v___x_2326_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2319_, v___x_2325_, v___x_2311_);
                crate::leanh::lean_inc_n(v___x_2318_, 2);
                v___x_2327_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2316_, v___x_2318_, v___x_2326_);
                v___x_2328_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2327_);
                v___x_2329_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__63;
                v___x_2330_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2330_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
                crate::leanh::lean_inc_ref_n(v___x_2330_, 2);
                crate::leanh::lean_inc_ref_n(v___x_2315_, 2);
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
                v___x_2335_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2333_);
                v___x_2336_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2334_, v___x_2335_);
                v___x_2337_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2336_);
                v___x_2338_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__64;
                v___x_2339_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__65;
                v___x_2340_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2340_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2340_, 1, v___x_2338_);
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
                v___x_2346_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2346_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                v___x_2347_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__45;
                v___x_2348_ = crate::leanh::lean_box(2);
                v___x_2349_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__47;
                v___x_2350_ = lean_mk_empty_array_with_capacity(v___x_2070_);
                v___x_2351_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__68);
                v___x_2352_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__69;
                v___x_2353_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__52;
                v___x_2354_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__53;
                v___x_2355_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2355_, 1, v___x_2354_);
                v___x_2356_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__71;
                v___x_2357_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__72;
                v_sz_2358_ = lean_array_size(v_args_2076_);
                v___x_2359_ = 0usize;
                crate::leanh::lean_inc_ref(v_args_2076_);
                v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1_spec__0(v_sz_2358_, v___x_2359_, v_args_2076_);
                v___x_2361_ = l_Array_append___redArg(v___x_2310_, v___x_2360_);
                crate::leanh::lean_dec_ref(v___x_2360_);
                v___x_2362_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2362_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2362_, 1, v___x_2300_);
                crate::leanh::lean_ctor_set(v___x_2362_, 2, v___x_2361_);
                crate::leanh::lean_inc_ref(v___x_2362_);
                v___x_2363_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2357_, v___x_2073_, v___x_2362_);
                v___x_2364_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__73;
                v___x_2365_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2365_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2365_, 1, v___x_2364_);
                v___x_2366_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2357_, v___x_2071_, v___x_2362_);
                crate::leanh::lean_inc(v___x_2366_);
                crate::leanh::lean_inc_ref(v___x_2365_);
                crate::leanh::lean_inc(v___x_2363_);
                v___x_2367_ = l_Lean_Syntax_node3(
                    v___x_2299_,
                    v___x_2356_,
                    v___x_2363_,
                    v___x_2365_,
                    v___x_2366_,
                );
                crate::leanh::lean_inc_ref(v___x_2355_);
                v___x_2368_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2353_, v___x_2355_, v___x_2367_);
                crate::leanh::lean_inc(v___x_2368_);
                v___x_2369_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v___x_2368_);
                v___x_2370_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2352_, v___x_2311_, v___x_2369_);
                v___x_2371_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__74;
                v___x_2372_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__6;
                v___x_2373_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2373_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2373_, 1, v___x_2372_);
                v___x_2374_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__76);
                v___x_2375_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__77;
                v___x_2376_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2375_, v_currMacroScope_2290_);
                v___x_2377_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__79;
                v___x_2378_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2378_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2378_, 1, v___x_2374_);
                crate::leanh::lean_ctor_set(v___x_2378_, 2, v___x_2376_);
                crate::leanh::lean_ctor_set(v___x_2378_, 3, v___x_2377_);
                v___x_2379_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__80;
                v___x_2380_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2379_, v___x_2311_, v___x_2311_);
                crate::leanh::lean_inc(v___x_2380_);
                crate::leanh::lean_inc_ref(v___x_2373_);
                v___x_2381_ = l_Lean_Syntax_node4(
                    v___x_2299_,
                    v___x_2371_,
                    v___x_2373_,
                    v___x_2378_,
                    v___x_2380_,
                    v___x_2311_,
                );
                crate::leanh::lean_inc(v___x_2381_);
                crate::leanh::lean_inc_ref(v___x_2346_);
                v___x_2382_ = l_Lean_Syntax_node5(
                    v___x_2299_,
                    v___x_2344_,
                    v___x_2346_,
                    v___x_2351_,
                    v___x_2370_,
                    v___x_2381_,
                    v___x_2311_,
                );
                crate::leanh::lean_inc(v___x_2343_);
                v___x_2383_ =
                    l_Lean_Syntax_node2(v___x_2299_, v___x_2308_, v___x_2343_, v___x_2382_);
                v___x_2384_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82_once), _init_l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__82);
                v___x_2385_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1___closed__83;
                v___x_2386_ =
                    l_Lean_addMacroScope(v_quotContext_2289_, v___x_2385_, v_currMacroScope_2290_);
                v___x_2387_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2299_);
                crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2384_);
                crate::leanh::lean_ctor_set(v___x_2387_, 2, v___x_2386_);
                crate::leanh::lean_ctor_set(v___x_2387_, 3, v___x_2323_);
                v___x_2388_ = l_Lean_Syntax_node1(v___x_2299_, v___x_2300_, v_unsafeMk_2293_);
                crate::leanh::lean_inc_ref(v___x_2387_);
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
                if crate::leanh::lean_obj_tag(v___y_2288_) == 1 {
                    v_val_2394_ = crate::leanh::lean_ctor_get(v___y_2288_, 0);
                    crate::leanh::lean_inc(v_val_2394_);
                    crate::leanh::lean_dec_ref_known(v___y_2288_, 1);
                    v___x_2395_ = l_Array_mkArray1___redArg(v_val_2394_);
                    crate::leanh::lean_inc(v_quotContext_2289_);
                    crate::leanh::lean_inc(v_currMacroScope_2290_);
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
                    crate::leanh::lean_dec(v___y_2288_);
                    v___x_2396_ = l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__nonemptyTypeCmd__1___closed__29;
                    crate::leanh::lean_inc(v_quotContext_2289_);
                    crate::leanh::lean_inc(v_currMacroScope_2290_);
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
                    v_reuseFailAlloc_2405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_val_2399_);
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
    mut v_x_2407_: *mut crate::leanh::LeanObject,
    mut v_a_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2410_ =
        l_Lake___aux__Lake__Util__OpaqueType______macroRules__Lake__hydrateOpaqueTypeCmd__1(
            v_x_2407_, v_a_2408_, v_a_2409_,
        );
    crate::leanh::lean_dec_ref(v_a_2408_);
    return v_res_2410_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OpaqueType(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OpaqueType(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_Binder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OpaqueType(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Binder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_OpaqueType(builtin);
}

// Lean compiler output
// Module: Lake.Build.Data
// Imports: Lake.Build.Key Lake.Util.Family Lake.Config.Dynlib Lake.Config.Kinds Lake.Config.Kinds Lake.Util.Name Lake.Config.Kinds Lake.Util.Name
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_string_append};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_TSyntax_getId, l_Lean_mkCIdentFrom, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_resolveNamespace,
    l_Lean_Macro_throwErrorAt___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getId, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_Syntax_node8, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::Build::Key::{
    initialize_Lake_Build_Key, runtime_initialize_Lake_Build_Key,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Config::Kinds::{
    initialize_Lake_Config_Kinds, l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace,
    l_Lake_Module_keyword, l_Lake_Package_keyword, runtime_initialize_Lake_Config_Kinds,
};
use crate::r#gen::Lake::Util::Family::{
    initialize_Lake_Util_Family, runtime_initialize_Lake_Util_Family,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_quoteFrom, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
pub static l_Lake_OptDataKind_instCoeOutName___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_OptDataKind_instCoeOutName___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OptDataKind_instCoeOutName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OptDataKind_instCoeOutName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_OptDataKind_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_OptDataKind_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OptDataKind_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OptDataKind_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_dataTypeDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__1_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [100, 97, 116, 97, 84, 121, 112, 101, 68, 101, 99, 108, 0],
    };
static mut l_Lake_dataTypeDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lake_dataTypeDecl___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_dataTypeDecl___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            1881956779838328975 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_dataTypeDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__5_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lake_dataTypeDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__7_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lake_dataTypeDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
            3961966953292576997 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__8_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_dataTypeDecl___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__11_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [100, 97, 116, 97, 95, 116, 121, 112, 101, 32, 0],
    };
static mut l_Lake_dataTypeDecl___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__11_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_dataTypeDecl___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__14_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lake_dataTypeDecl___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__14_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__15_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_dataTypeDecl___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__18_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lake_dataTypeDecl___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__18_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_dataTypeDecl___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__21_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_dataTypeDecl___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__21_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__23_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__22_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__20_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_dataTypeDecl___closed__25_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_dataTypeDecl___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__25_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_dataTypeDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 97, 109, 105, 108, 121, 95, 100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__6_value) as *mut crate::leanh::LeanObject,8497769072906204829 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__8_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10_value) as *mut crate::leanh::LeanObject,10411423847645546083 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12_value) as *mut crate::leanh::LeanObject,11064845058293668901 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17_value) as *mut crate::leanh::LeanObject,5940551064397964566 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 75, 105, 110, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value
) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value) as *mut crate::leanh::LeanObject,16416955358139906133 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23_value) as *mut crate::leanh::LeanObject,2323862020472801593 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__28_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__27_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31_value) as *mut crate::leanh::LeanObject,13585030837571646948 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__33_value) as *mut crate::leanh::LeanObject,13429426995999683896 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__37_value) as *mut crate::leanh::LeanObject,16173796135615239867 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__41_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__43_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45_value) as *mut crate::leanh::LeanObject,12783917532758215986 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__47_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__40_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__50_value) as *mut crate::leanh::LeanObject,7383208167966365478 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [78, 97, 109, 101, 46, 105, 115, 65, 110, 111, 110, 121, 109, 111, 117, 115, 95, 105, 102, 102, 95, 101, 113, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52_value
) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [78, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [105, 115, 65, 110, 111, 110, 121, 109, 111, 117, 115, 95, 105, 102, 102, 95, 101, 113, 95, 97, 110, 111, 110, 121, 109, 111, 117, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value) as *mut crate::leanh::LeanObject,7623807776322335386 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value) as *mut crate::leanh::LeanObject,18384533828395609354 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__54_value) as *mut crate::leanh::LeanObject,4969359694978789214 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__55_value) as *mut crate::leanh::LeanObject,15756887508575660446 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__57_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__58_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62_value) as *mut crate::leanh::LeanObject,7625897890118033792 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63_value) as *mut crate::leanh::LeanObject,8715860392475343861 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 84, 121, 112, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__65_value) as *mut crate::leanh::LeanObject,10991155264597083169 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__67_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 97, 109, 105, 108, 121, 68, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69_value) as *mut crate::leanh::LeanObject,11046805638130364475 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70_value
) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindUnit___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lake_instDataKindUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindUnit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10978858759480610910 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindUnit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindUnit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindBool___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [98, 111, 111, 108, 0],
    };
static mut l_Lake_instDataKindBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindBool___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instDataKindBool___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11722710492834003908 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindBool___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindBool___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindFilePath___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [102, 105, 108, 101, 112, 97, 116, 104, 0],
    };
static mut l_Lake_instDataKindFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindFilePath___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18237634648366862254 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindFilePath___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindFilePath___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindDynlib___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [100, 121, 110, 108, 105, 98, 0],
    };
static mut l_Lake_instDataKindDynlib___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindDynlib___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14454008108361683552 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindDynlib___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindDynlib: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindDynlib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            98, 117, 105, 108, 116, 105, 110, 70, 97, 99, 101, 116, 67, 111, 109, 109, 97, 110,
            100, 0,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_builtinFacetCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_builtinFacetCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4395217195902989964 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__2_value: crate::leanh::LeanStringObject<15> =
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
            98, 117, 105, 108, 116, 105, 110, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__5_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lake_builtinFacetCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__5_value)
                as *mut crate::leanh::LeanObject,
            4024150434455327032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__7_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lake_builtinFacetCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__7_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__9_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 64, 32, 0],
    };
static mut l_Lake_builtinFacetCommand___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__10_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__13_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__19_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lake_builtinFacetCommand___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__21_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__21_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_builtinFacetCommand___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_builtinFacetCommand___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_builtinFacetCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_builtinFacetCommand___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,7045040058828669725 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 115, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,9363914857124557226 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 97, 109, 105, 108, 121, 68, 101, 102, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut crate::leanh::LeanObject,14062987408811487381 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__21_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 43, 43, 95, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__25_value) as *mut crate::leanh::LeanObject,1718176677342102874 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [43, 43, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 102, 101, 114, 73, 110, 115, 116, 97, 110, 99, 101, 65, 115, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [99, 97, 110, 110, 111, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 102, 97, 99, 101, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 114, 111, 109, 32, 102, 97, 99, 101, 116, 32, 110, 97, 109, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 99, 101, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 97, 99, 101, 116, 79, 117, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0_value) as *mut crate::leanh::LeanObject,18435903728707736368 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 116, 97, 114, 103, 101, 116, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 111, 114, 32, 97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 116, 97, 114, 103, 101, 116, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 32, 96, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [102, 97, 99, 101, 116, 68, 97, 116, 97, 68, 101, 99, 108, 0],
    };
static mut l_Lake_facetDataDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_facetDataDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_facetDataDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6050667296239256698 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [102, 97, 99, 101, 116, 95, 100, 97, 116, 97, 32, 0],
    };
static mut l_Lake_facetDataDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_facetDataDecl___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_facetDataDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_facetDataDecl___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_facetDataDecl___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_facetDataDecl___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__9_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_facetDataDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_facetDataDecl___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15_value) as *mut crate::leanh::LeanObject,13678286827328889081 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29_value) as *mut crate::leanh::LeanObject,5279388724434323336 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__0_value: crate::leanh::LeanStringObject<16> =
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
            112, 97, 99, 107, 97, 103, 101, 68, 97, 116, 97, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_packageDataDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_packageDataDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_packageDataDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2082768154632822931 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [112, 97, 99, 107, 97, 103, 101, 95, 100, 97, 116, 97, 32, 0],
    };
static mut l_Lake_packageDataDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_packageDataDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_packageDataDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_packageDataDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_packageDataDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_packageDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 97, 99, 101, 116, 95, 100, 97, 116, 97, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__0_value: crate::leanh::LeanStringObject<15> =
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
            109, 111, 100, 117, 108, 101, 68, 97, 116, 97, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_moduleDataDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_moduleDataDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13351734753328622778 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [109, 111, 100, 117, 108, 101, 95, 100, 97, 116, 97, 32, 0],
    };
static mut l_Lake_moduleDataDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_moduleDataDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_moduleDataDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_moduleDataDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_moduleDataDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_moduleDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__0_value: crate::leanh::LeanStringObject<16> =
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
            108, 105, 98, 114, 97, 114, 121, 68, 97, 116, 97, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_libraryDataDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_libraryDataDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13678170361092144735 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__2_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [108, 105, 98, 114, 97, 114, 121, 95, 100, 97, 116, 97, 32, 0],
    };
static mut l_Lake_libraryDataDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_libraryDataDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_libraryDataDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_libraryDataDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_libraryDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__0_value) as *mut crate::leanh::LeanObject,12295998048739818339 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__0_value: crate::leanh::LeanStringObject<15> =
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
            99, 117, 115, 116, 111, 109, 68, 97, 116, 97, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_customDataDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_customDataDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_customDataDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4714469286443954978 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [99, 117, 115, 116, 111, 109, 95, 100, 97, 116, 97, 32, 0],
    };
static mut l_Lake_customDataDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_customDataDecl___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_customDataDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_customDataDecl___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_customDataDecl___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_customDataDecl___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__9_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_customDataDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_customDataDecl___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__0_value) as *mut crate::leanh::LeanObject,15644373471618144447 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 117, 115, 116, 111, 109, 79, 117, 116, 0]};
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_dataTypeDecl___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__4_value) as *mut crate::leanh::LeanObject,10715840225401224552 as *mut crate::leanh::LeanObject] };
static mut l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_OptDataKind_anonymous(
    mut v_00_u03b1_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = crate::leanh::lean_box(0);
    return v___x_1528_;
}
pub unsafe fn l_Lake_OptDataKind_instInhabited(
    mut v_00_u03b1_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = crate::leanh::lean_box(0);
    return v___x_1530_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___redArg(
    mut v_self_1531_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1532_: u8 = 0;
    v___x_1532_ = l_Lean_Name_isAnonymous(v_self_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___redArg___boxed(
    mut v_self_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: u8 = 0;
    let mut v_r_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lake_OptDataKind_isAnonymous___redArg(v_self_1533_);
    crate::leanh::lean_dec(v_self_1533_);
    v_r_1535_ = crate::leanh::lean_box((v_res_1534_) as usize);
    return v_r_1535_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous(
    mut v_00_u03b1_1536_: *mut crate::leanh::LeanObject,
    mut v_self_1537_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1538_: u8 = 0;
    v___x_1538_ = l_Lean_Name_isAnonymous(v_self_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Lake_OptDataKind_isAnonymous___boxed(
    mut v_00_u03b1_1539_: *mut crate::leanh::LeanObject,
    mut v_self_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: u8 = 0;
    let mut v_r_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lake_OptDataKind_isAnonymous(v_00_u03b1_1539_, v_self_1540_);
    crate::leanh::lean_dec(v_self_1540_);
    v_r_1542_ = crate::leanh::lean_box((v_res_1541_) as usize);
    return v_r_1542_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___redArg(
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1543_);
    return v_inst_1543_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___redArg___boxed(
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Lake_OptDataKind_instOfDataKind___redArg(v_inst_1544_);
    crate::leanh::lean_dec(v_inst_1544_);
    return v_res_1545_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind(
    mut v_00_u03b1_1546_: *mut crate::leanh::LeanObject,
    mut v_inst_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1547_);
    return v_inst_1547_;
}
pub unsafe fn l_Lake_OptDataKind_instOfDataKind___boxed(
    mut v_00_u03b1_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_OptDataKind_instOfDataKind(v_00_u03b1_1548_, v_inst_1549_);
    crate::leanh::lean_dec(v_inst_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName___lam__0(
    mut v_x_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1551_);
    return v_x_1551_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName___lam__0___boxed(
    mut v_x_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Lake_OptDataKind_instCoeOutName___lam__0(v_x_1552_);
    crate::leanh::lean_dec(v_x_1552_);
    return v_res_1553_;
}
pub unsafe fn l_Lake_OptDataKind_instCoeOutName(
    mut v_00_u03b1_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1556_ = l_Lake_OptDataKind_instCoeOutName___closed__0;
    return v___f_1556_;
}
pub unsafe fn l_Lake_OptDataKind_instToString___lam__0(
    mut v_x_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = 1;
    v___x_1559_ = l_Lean_Name_toString(v_x_1557_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Lake_OptDataKind_instToString(
    mut v_00_u03b1_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1562_ = l_Lake_OptDataKind_instToString___closed__0;
    return v___f_1562_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__23;
    v___x_1677_ = l_String_toRawSubstring_x27(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__52;
    v___x_1749_ = l_String_toRawSubstring_x27(v___x_1748_);
    return v___x_1749_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1785_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(
    mut v_x_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1791_ = l_Lake_dataTypeDecl___closed__2;
                crate::leanh::lean_inc(v_x_1788_);
                v___x_1792_ = l_Lean_Syntax_isOfKind(v_x_1788_, v___x_1791_);
                if v___x_1792_ == 0 {
                    crate::leanh::lean_dec(v_x_1788_);
                    v___x_1793_ = crate::leanh::lean_box(1);
                    v___x_1794_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1793_);
                    crate::leanh::lean_ctor_set(v___x_1794_, 1, v_a_1790_);
                    return v___x_1794_;
                } else {
                    v___x_1795_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1796_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1795_);
                    v___x_1797_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_kind_1798_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1797_);
                    v___x_1799_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1800_ = l_Lean_Syntax_getArg(v_x_1788_, v___x_1799_);
                    crate::leanh::lean_dec(v_x_1788_);
                    v___x_1908_ = l_Lean_Syntax_getOptional_x3f(v___x_1796_);
                    crate::leanh::lean_dec(v___x_1796_);
                    if crate::leanh::lean_obj_tag(v___x_1908_) == 0 {
                        v___x_1909_ = crate::leanh::lean_box(0);
                        v___y_1892_ = v___x_1909_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1910_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                        v_isSharedCheck_1917_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                        if v_isSharedCheck_1917_ == 0 {
                            v___x_1912_ = v___x_1908_;
                            v_isShared_1913_ = v_isSharedCheck_1917_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1910_);
                            crate::leanh::lean_dec(v___x_1908_);
                            v___x_1912_ = crate::leanh::lean_box(0);
                            v_isShared_1913_ = v_isSharedCheck_1917_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_1806_, 2);
                v___x_1811_ = l_Array_append___redArg(v___y_1806_, v___y_1810_);
                crate::leanh::lean_dec_ref(v___y_1810_);
                crate::leanh::lean_inc_n(v___y_1808_, 9);
                crate::leanh::lean_inc_n(v___y_1805_, 40);
                v___x_1812_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1812_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1812_, 1, v___y_1808_);
                crate::leanh::lean_ctor_set(v___x_1812_, 2, v___x_1811_);
                v___x_1813_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_1814_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1814_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                v___x_1815_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_1816_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1816_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
                v___x_1817_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_1818_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1818_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1818_, 1, v___x_1817_);
                crate::leanh::lean_inc(v___x_1800_);
                crate::leanh::lean_inc_ref(v___x_1818_);
                crate::leanh::lean_inc(v___y_1803_);
                crate::leanh::lean_inc_ref(v___x_1816_);
                crate::leanh::lean_inc(v___y_1804_);
                v___x_1819_ = l_Lean_Syntax_node8(
                    v___y_1805_,
                    v___y_1804_,
                    v___x_1812_,
                    v___x_1814_,
                    v_kind_1798_,
                    v___x_1816_,
                    v___y_1807_,
                    v___y_1803_,
                    v___x_1818_,
                    v___x_1800_,
                );
                v___x_1820_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_1821_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_1822_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1822_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1822_, 1, v___y_1808_);
                crate::leanh::lean_ctor_set(v___x_1822_, 2, v___y_1806_);
                v___x_1823_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                v___x_1824_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11;
                v___x_1825_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1825_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1825_, 1, v___x_1823_);
                v___x_1826_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1824_, v___x_1825_);
                v___x_1827_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1826_);
                crate::leanh::lean_inc_ref_n(v___x_1822_, 18);
                v___x_1828_ = l_Lean_Syntax_node7(
                    v___y_1805_,
                    v___x_1821_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1827_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1822_,
                );
                v___x_1829_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_1830_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13;
                v___x_1831_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16;
                v___x_1832_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1831_, v___x_1822_);
                v___x_1833_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1833_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1833_, 1, v___x_1829_);
                v___x_1834_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18;
                v___x_1835_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20;
                v___x_1836_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22;
                v___x_1837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__24);
                v___x_1838_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__25;
                crate::leanh::lean_inc_n(v___y_1802_, 2);
                crate::leanh::lean_inc_n(v___y_1809_, 2);
                v___x_1839_ = l_Lean_addMacroScope(v___y_1809_, v___x_1838_, v___y_1802_);
                v___x_1840_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__30;
                v___x_1841_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1841_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1841_, 1, v___x_1837_);
                crate::leanh::lean_ctor_set(v___x_1841_, 2, v___x_1839_);
                crate::leanh::lean_ctor_set(v___x_1841_, 3, v___x_1840_);
                v___x_1842_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1800_);
                v___x_1843_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1836_, v___x_1841_, v___x_1842_);
                v___x_1844_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1835_, v___x_1816_, v___x_1843_);
                v___x_1845_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1834_, v___x_1822_, v___x_1844_);
                v___x_1846_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32;
                v___x_1847_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__34;
                v___x_1848_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__35;
                v___x_1849_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1849_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1848_);
                v___x_1850_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_1851_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1851_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
                v___x_1852_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__38;
                v___x_1853_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__39;
                v___x_1854_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1854_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1854_, 1, v___x_1853_);
                v___x_1855_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__42;
                v___x_1856_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__44;
                v___x_1857_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__45;
                v___x_1858_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__46;
                v___x_1859_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1859_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1857_);
                v___x_1860_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__48;
                v___x_1861_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1860_, v___x_1822_);
                v___x_1862_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__49;
                v___x_1863_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__51;
                v___x_1865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__53);
                v___x_1866_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__56;
                v___x_1867_ = l_Lean_addMacroScope(v___y_1809_, v___x_1866_, v___y_1802_);
                v___x_1868_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__59;
                v___x_1869_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1869_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1869_, 1, v___x_1865_);
                crate::leanh::lean_ctor_set(v___x_1869_, 2, v___x_1867_);
                crate::leanh::lean_ctor_set(v___x_1869_, 3, v___x_1868_);
                v___x_1870_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___x_1864_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1869_,
                );
                v___x_1871_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1870_);
                v___x_1872_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60;
                v___x_1873_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1873_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1873_, 1, v___x_1872_);
                v___x_1874_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___y_1808_,
                    v___x_1863_,
                    v___x_1871_,
                    v___x_1873_,
                );
                v___x_1875_ = l_Lean_Syntax_node6(
                    v___y_1805_,
                    v___x_1858_,
                    v___x_1859_,
                    v___x_1861_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1874_,
                    v___x_1822_,
                );
                v___x_1876_ = l_Lean_Syntax_node1(v___y_1805_, v___y_1808_, v___x_1875_);
                v___x_1877_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1856_, v___x_1876_);
                v___x_1878_ = l_Lean_Syntax_node1(v___y_1805_, v___x_1855_, v___x_1877_);
                v___x_1879_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1852_, v___x_1854_, v___x_1878_);
                v___x_1880_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___y_1808_,
                    v___y_1803_,
                    v___x_1851_,
                    v___x_1879_,
                );
                v___x_1881_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__61;
                v___x_1882_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1882_, 0, v___y_1805_);
                crate::leanh::lean_ctor_set(v___x_1882_, 1, v___x_1881_);
                v___x_1883_ = l_Lean_Syntax_node3(
                    v___y_1805_,
                    v___x_1847_,
                    v___x_1849_,
                    v___x_1880_,
                    v___x_1882_,
                );
                v___x_1884_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64;
                v___x_1885_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1884_, v___x_1822_, v___x_1822_);
                v___x_1886_ = l_Lean_Syntax_node4(
                    v___y_1805_,
                    v___x_1846_,
                    v___x_1818_,
                    v___x_1883_,
                    v___x_1885_,
                    v___x_1822_,
                );
                v___x_1887_ = l_Lean_Syntax_node6(
                    v___y_1805_,
                    v___x_1830_,
                    v___x_1832_,
                    v___x_1833_,
                    v___x_1822_,
                    v___x_1822_,
                    v___x_1845_,
                    v___x_1886_,
                );
                v___x_1888_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___x_1820_, v___x_1828_, v___x_1887_);
                v___x_1889_ =
                    l_Lean_Syntax_node2(v___y_1805_, v___y_1808_, v___x_1819_, v___x_1888_);
                v___x_1890_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1890_, 0, v___x_1889_);
                crate::leanh::lean_ctor_set(v___x_1890_, 1, v_a_1790_);
                return v___x_1890_;
            }
            2 => {
                v_quotContext_1893_ = crate::leanh::lean_ctor_get(v_a_1789_, 1);
                v_currMacroScope_1894_ = crate::leanh::lean_ctor_get(v_a_1789_, 2);
                v_ref_1895_ = crate::leanh::lean_ctor_get(v_a_1789_, 5);
                v___x_1896_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__66;
                v___x_1897_ = 0;
                v___x_1898_ = l_Lean_mkCIdentFrom(v_ref_1895_, v___x_1896_, v___x_1897_);
                v___x_1899_ = l_Lean_TSyntax_getId(v_kind_1798_);
                crate::leanh::lean_inc(v_kind_1798_);
                v___x_1900_ = l_Lake_Name_quoteFrom(v_kind_1798_, v___x_1899_, v___x_1897_);
                v___x_1901_ = l_Lean_SourceInfo_fromRef(v_ref_1895_, v___x_1897_);
                v___x_1902_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_1903_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_1904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_1892_) == 1 {
                    v_val_1905_ = crate::leanh::lean_ctor_get(v___y_1892_, 0);
                    crate::leanh::lean_inc(v_val_1905_);
                    crate::leanh::lean_dec_ref_known(v___y_1892_, 1);
                    v___x_1906_ = l_Array_mkArray1___redArg(v_val_1905_);
                    v___y_1802_ = v_currMacroScope_1894_;
                    v___y_1803_ = v___x_1900_;
                    v___y_1804_ = v___x_1903_;
                    v___y_1805_ = v___x_1901_;
                    v___y_1806_ = v___x_1904_;
                    v___y_1807_ = v___x_1898_;
                    v___y_1808_ = v___x_1902_;
                    v___y_1809_ = v_quotContext_1893_;
                    v___y_1810_ = v___x_1906_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1892_);
                    v___x_1907_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_1802_ = v_currMacroScope_1894_;
                    v___y_1803_ = v___x_1900_;
                    v___y_1804_ = v___x_1903_;
                    v___y_1805_ = v___x_1901_;
                    v___y_1806_ = v___x_1904_;
                    v___y_1807_ = v___x_1898_;
                    v___y_1808_ = v___x_1902_;
                    v___y_1809_ = v_quotContext_1893_;
                    v___y_1810_ = v___x_1907_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1913_ == 0 {
                    v___x_1915_ = v___x_1912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_val_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1892_ = v___x_1915_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___boxed(
    mut v_x_1918_: *mut crate::leanh::LeanObject,
    mut v_a_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1921_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1(
        v_x_1918_, v_a_1919_, v_a_1920_,
    );
    crate::leanh::lean_dec_ref(v_a_1919_);
    return v_res_1921_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__5;
    v___x_2010_ = l_String_toRawSubstring_x27(v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2014_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__8;
    v___x_2015_ = l_String_toRawSubstring_x27(v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15;
    v___x_2024_ = l_String_toRawSubstring_x27(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__23;
    v___x_2035_ = l_String_toRawSubstring_x27(v___x_2034_);
    return v___x_2035_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(
    mut v___x_2044_: *mut crate::leanh::LeanObject,
    mut v___x_2045_: *mut crate::leanh::LeanObject,
    mut v___x_2046_: *mut crate::leanh::LeanObject,
    mut v_fam_2047_: *mut crate::leanh::LeanObject,
    mut v___x_2048_: *mut crate::leanh::LeanObject,
    mut v___x_2049_: *mut crate::leanh::LeanObject,
    mut v___x_2050_: *mut crate::leanh::LeanObject,
    mut v___x_2051_: u8,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v_name_2053_: *mut crate::leanh::LeanObject,
    mut v_ns_2054_: *mut crate::leanh::LeanObject,
    mut v___x_2055_: *mut crate::leanh::LeanObject,
    mut v___x_2056_: u8,
    mut v_tk_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___x_2059_: *mut crate::leanh::LeanObject,
    mut v_____r_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: u8 = 0;
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2256_ = l_Lean_TSyntax_getId(v_name_2053_);
                if crate::leanh::lean_obj_tag(v___y_2058_) == 0 {
                    v___y_2258_ = v___x_2051_;
                    state = 4;
                    continue;
                } else {
                    v___y_2258_ = v___x_2056_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_2078_, 2);
                v___x_2081_ = l_Array_append___redArg(v___y_2078_, v___y_2080_);
                crate::leanh::lean_dec_ref(v___y_2080_);
                crate::leanh::lean_inc_n(v___y_2072_, 9);
                crate::leanh::lean_inc_n(v___y_2065_, 53);
                v___x_2082_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2082_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2082_, 1, v___y_2072_);
                crate::leanh::lean_ctor_set(v___x_2082_, 2, v___x_2081_);
                v___x_2083_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__14;
                v___x_2084_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_2066_, 17);
                crate::leanh::lean_inc_ref_n(v___y_2075_, 18);
                v___x_2085_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2084_);
                v___x_2086_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__1;
                v___x_2087_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2087_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2087_, 1, v___x_2086_);
                v___x_2088_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__2;
                v___x_2089_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2088_);
                v___x_2090_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__15;
                v___x_2091_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2090_);
                v___x_2092_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2092_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2092_, 1, v___y_2072_);
                crate::leanh::lean_ctor_set(v___x_2092_, 2, v___y_2078_);
                crate::leanh::lean_inc_ref_n(v___x_2092_, 23);
                v___x_2093_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2091_, v___x_2092_);
                v___x_2094_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__3;
                v___x_2095_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__4;
                v___x_2096_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2094_, v___x_2095_);
                v___x_2097_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__6);
                v___x_2098_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__7;
                crate::leanh::lean_inc_n(v___y_2064_, 5);
                crate::leanh::lean_inc_n(v___y_2068_, 5);
                v___x_2099_ = l_Lean_addMacroScope(v___y_2068_, v___x_2098_, v___y_2064_);
                v___x_2100_ = crate::leanh::lean_box(0);
                v___x_2101_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2101_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2101_, 1, v___x_2097_);
                crate::leanh::lean_ctor_set(v___x_2101_, 2, v___x_2099_);
                crate::leanh::lean_ctor_set(v___x_2101_, 3, v___x_2100_);
                crate::leanh::lean_inc(v___x_2096_);
                v___x_2102_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2096_, v___x_2101_, v___x_2092_);
                crate::leanh::lean_inc_n(v___x_2093_, 2);
                crate::leanh::lean_inc(v___x_2089_);
                v___x_2103_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2089_, v___x_2093_, v___x_2102_);
                v___x_2104_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_2105_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2105_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                v___x_2106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__9);
                v___x_2107_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__10;
                v___x_2108_ = l_Lean_addMacroScope(v___y_2068_, v___x_2107_, v___y_2064_);
                v___x_2109_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2109_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2109_, 1, v___x_2106_);
                crate::leanh::lean_ctor_set(v___x_2109_, 2, v___x_2108_);
                crate::leanh::lean_ctor_set(v___x_2109_, 3, v___x_2100_);
                v___x_2110_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2096_, v___x_2109_, v___x_2092_);
                v___x_2111_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2089_, v___x_2093_, v___x_2110_);
                v___x_2112_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2103_,
                    v___x_2105_,
                    v___x_2111_,
                );
                v___x_2113_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__60;
                v___x_2114_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2114_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2114_, 1, v___x_2113_);
                v___x_2115_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2085_,
                    v___x_2087_,
                    v___x_2112_,
                    v___x_2114_,
                );
                v___x_2116_ = l_Lean_Syntax_node1(v___y_2065_, v___y_2072_, v___x_2115_);
                v___x_2117_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                crate::leanh::lean_inc_ref_n(v___y_2076_, 7);
                v___x_2118_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2117_);
                v___x_2119_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2119_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2119_, 1, v___x_2117_);
                v___x_2120_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2118_, v___x_2119_);
                v___x_2121_ = l_Lean_Syntax_node1(v___y_2065_, v___y_2072_, v___x_2120_);
                crate::leanh::lean_inc(v___x_2121_);
                crate::leanh::lean_inc_n(v___y_2074_, 2);
                v___x_2122_ = l_Lean_Syntax_node7(
                    v___y_2065_,
                    v___y_2074_,
                    v___x_2082_,
                    v___x_2116_,
                    v___x_2121_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                );
                v___x_2123_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__11;
                v___x_2124_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2123_);
                v___x_2125_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__12;
                v___x_2126_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2126_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2125_);
                v___x_2127_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__13;
                v___x_2128_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2127_);
                v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2044_);
                v___x_2130_ = crate::leanh::lean_box(2);
                v___x_2131_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2131_, 0, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2131_, 1, v___y_2072_);
                crate::leanh::lean_ctor_set(v___x_2131_, 2, v___x_2129_);
                v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2045_);
                v___x_2133_ = lean_array_push(v___x_2132_, v___y_2070_);
                v___x_2134_ = lean_array_push(v___x_2133_, v___x_2131_);
                v___x_2135_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2128_);
                crate::leanh::lean_ctor_set(v___x_2135_, 2, v___x_2134_);
                v___x_2136_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__14;
                v___x_2137_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2136_);
                v___x_2138_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2137_, v___x_2092_, v___x_2092_);
                v___x_2139_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__31;
                v___x_2140_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2139_);
                v___x_2141_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_2142_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2142_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
                v___x_2143_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__62;
                v___x_2144_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__63;
                v___x_2145_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2143_, v___x_2144_);
                v___x_2146_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2145_, v___x_2092_, v___x_2092_);
                crate::leanh::lean_inc(v___x_2146_);
                crate::leanh::lean_inc_n(v___y_2079_, 2);
                crate::leanh::lean_inc_ref_n(v___x_2142_, 2);
                crate::leanh::lean_inc(v___x_2140_);
                v___x_2147_ = l_Lean_Syntax_node4(
                    v___y_2065_,
                    v___x_2140_,
                    v___x_2142_,
                    v___y_2079_,
                    v___x_2146_,
                    v___x_2092_,
                );
                v___x_2148_ = l_Lean_Syntax_node5(
                    v___y_2065_,
                    v___x_2124_,
                    v___x_2126_,
                    v___x_2135_,
                    v___x_2138_,
                    v___x_2147_,
                    v___x_2092_,
                );
                crate::leanh::lean_inc_n(v___y_2069_, 2);
                v___x_2149_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___y_2069_, v___x_2122_, v___x_2148_);
                v___x_2150_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__69;
                crate::leanh::lean_inc_ref_n(v___x_2046_, 2);
                v___x_2151_ = l_Lean_Name_mkStr2(v___x_2046_, v___x_2150_);
                v___x_2152_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2153_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                v___x_2154_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2155_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2155_, 1, v___x_2154_);
                crate::leanh::lean_inc_n(v___x_2048_, 2);
                crate::leanh::lean_inc_ref(v___x_2155_);
                v___x_2156_ = l_Lean_Syntax_node8(
                    v___y_2065_,
                    v___x_2151_,
                    v___x_2092_,
                    v___x_2153_,
                    v___y_2073_,
                    v___x_2155_,
                    v_fam_2047_,
                    v___y_2079_,
                    v___x_2142_,
                    v___x_2048_,
                );
                v___x_2157_ = l_Lean_Syntax_node7(
                    v___y_2065_,
                    v___y_2074_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2121_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2092_,
                );
                v___x_2158_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_2159_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2158_);
                v___x_2160_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2160_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2160_, 1, v___x_2158_);
                v___x_2161_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__17;
                v___x_2162_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___y_2076_, v___x_2161_);
                v___x_2163_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__19;
                v___x_2164_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2163_);
                v___x_2165_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__21;
                v___x_2166_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2165_);
                v___x_2167_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__15;
                v___x_2168_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
                v___x_2169_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17;
                v___x_2170_ = l_Lean_addMacroScope(v___y_2068_, v___x_2169_, v___y_2064_);
                v___x_2171_ = l_Lean_Name_mkStr2(v___x_2046_, v___x_2167_);
                crate::leanh::lean_inc(v___x_2171_);
                v___x_2172_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2172_, 0, v___x_2171_);
                crate::leanh::lean_ctor_set(v___x_2172_, 1, v___x_2100_);
                v___x_2173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2171_);
                v___x_2174_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2173_);
                crate::leanh::lean_ctor_set(v___x_2174_, 1, v___x_2100_);
                v___x_2175_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2175_, 0, v___x_2172_);
                crate::leanh::lean_ctor_set(v___x_2175_, 1, v___x_2174_);
                v___x_2176_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2176_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2168_);
                crate::leanh::lean_ctor_set(v___x_2176_, 2, v___x_2170_);
                crate::leanh::lean_ctor_set(v___x_2176_, 3, v___x_2175_);
                crate::leanh::lean_inc_ref(v___x_2049_);
                v___x_2177_ = l_String_toRawSubstring_x27(v___x_2049_);
                v___x_2178_ = l_Lean_Name_mkStr1(v___x_2049_);
                v___x_2179_ = l_Lean_addMacroScope(v___y_2068_, v___x_2178_, v___y_2064_);
                v___x_2180_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2050_);
                crate::leanh::lean_ctor_set(v___x_2180_, 1, v___x_2100_);
                v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set(v___x_2181_, 1, v___x_2100_);
                v___x_2182_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2182_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2182_, 1, v___x_2177_);
                crate::leanh::lean_ctor_set(v___x_2182_, 2, v___x_2179_);
                crate::leanh::lean_ctor_set(v___x_2182_, 3, v___x_2181_);
                v___x_2183_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__18;
                v___x_2184_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2183_);
                v___x_2185_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__19;
                v___x_2186_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2185_);
                v___x_2187_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2188_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2188_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2188_, 1, v___x_2187_);
                v___x_2189_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2190_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_2191_ = crate::leanh::lean_box(0);
                v___x_2192_ = l_Lean_addMacroScope(v___y_2068_, v___x_2191_, v___y_2064_);
                v___x_2193_ = l_Lean_Name_mkStr1(v___x_2046_);
                v___x_2194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2194_, 0, v___x_2193_);
                v___x_2195_ = l_Lean_Name_mkStr1(v___y_2075_);
                v___x_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2196_, 0, v___x_2195_);
                v___x_2197_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2196_);
                crate::leanh::lean_ctor_set(v___x_2197_, 1, v___x_2100_);
                v___x_2198_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2194_);
                crate::leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
                v___x_2199_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2199_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2190_);
                crate::leanh::lean_ctor_set(v___x_2199_, 2, v___x_2192_);
                crate::leanh::lean_ctor_set(v___x_2199_, 3, v___x_2198_);
                v___x_2200_ = l_Lean_Syntax_node1(v___y_2065_, v___x_2189_, v___x_2199_);
                v___x_2201_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2186_, v___x_2188_, v___x_2200_);
                v___x_2202_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26;
                v___x_2203_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27;
                v___x_2204_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2204_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2204_, 1, v___x_2203_);
                v___x_2205_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2202_,
                    v___y_2077_,
                    v___x_2204_,
                    v___y_2071_,
                );
                v___x_2206_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_2207_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2207_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2207_, 1, v___x_2206_);
                crate::leanh::lean_inc_ref(v___x_2207_);
                crate::leanh::lean_inc(v___x_2201_);
                crate::leanh::lean_inc(v___x_2184_);
                v___x_2208_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2184_,
                    v___x_2201_,
                    v___x_2205_,
                    v___x_2207_,
                );
                crate::leanh::lean_inc_ref(v___x_2182_);
                v___x_2209_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2182_,
                    v___x_2208_,
                    v___x_2048_,
                );
                crate::leanh::lean_inc_ref(v___x_2176_);
                crate::leanh::lean_inc(v___x_2166_);
                v___x_2210_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2166_, v___x_2176_, v___x_2209_);
                v___x_2211_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2164_, v___x_2155_, v___x_2210_);
                v___x_2212_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2162_, v___x_2092_, v___x_2211_);
                v___x_2213_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29;
                v___x_2214_ =
                    l_Lean_Name_mkStr4(v___y_2075_, v___y_2066_, v___x_2083_, v___x_2213_);
                v___x_2215_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2215_, 0, v___y_2065_);
                crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2213_);
                v___x_2216_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2182_,
                    v___y_2079_,
                    v___x_2048_,
                );
                v___x_2217_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2166_, v___x_2176_, v___x_2216_);
                v___x_2218_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___x_2184_,
                    v___x_2201_,
                    v___x_2217_,
                    v___x_2207_,
                );
                v___x_2219_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___x_2214_, v___x_2215_, v___x_2218_);
                v___x_2220_ = l_Lean_Syntax_node4(
                    v___y_2065_,
                    v___x_2140_,
                    v___x_2142_,
                    v___x_2219_,
                    v___x_2146_,
                    v___x_2092_,
                );
                v___x_2221_ = l_Lean_Syntax_node6(
                    v___y_2065_,
                    v___x_2159_,
                    v___x_2093_,
                    v___x_2160_,
                    v___x_2092_,
                    v___x_2092_,
                    v___x_2212_,
                    v___x_2220_,
                );
                v___x_2222_ =
                    l_Lean_Syntax_node2(v___y_2065_, v___y_2069_, v___x_2157_, v___x_2221_);
                v___x_2223_ = l_Lean_Syntax_node3(
                    v___y_2065_,
                    v___y_2072_,
                    v___x_2149_,
                    v___x_2156_,
                    v___x_2222_,
                );
                v___x_2224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
                crate::leanh::lean_ctor_set(v___x_2224_, 1, v___y_2067_);
                return v___x_2224_;
            }
            2 => {
                v_quotContext_2233_ = crate::leanh::lean_ctor_get(v___y_2231_, 1);
                v_currMacroScope_2234_ = crate::leanh::lean_ctor_get(v___y_2231_, 2);
                v_ref_2235_ = crate::leanh::lean_ctor_get(v___y_2231_, 5);
                v___x_2236_ = l_Lean_SourceInfo_fromRef(v_ref_2235_, v___x_2051_);
                v___x_2237_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2238_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__3;
                v___x_2239_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__4;
                v___x_2240_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__5;
                v___x_2241_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_2242_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_2243_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_2052_) == 1 {
                    v_val_2244_ = crate::leanh::lean_ctor_get(v___y_2052_, 0);
                    crate::leanh::lean_inc(v_val_2244_);
                    crate::leanh::lean_dec_ref_known(v___y_2052_, 1);
                    v___x_2245_ = l_Array_mkArray1___redArg(v_val_2244_);
                    v___y_2064_ = v_currMacroScope_2234_;
                    v___y_2065_ = v___x_2236_;
                    v___y_2066_ = v___x_2239_;
                    v___y_2067_ = v___y_2232_;
                    v___y_2068_ = v_quotContext_2233_;
                    v___y_2069_ = v___x_2241_;
                    v___y_2070_ = v_id_2230_;
                    v___y_2071_ = v___y_2226_;
                    v___y_2072_ = v___x_2237_;
                    v___y_2073_ = v___y_2227_;
                    v___y_2074_ = v___x_2242_;
                    v___y_2075_ = v___x_2238_;
                    v___y_2076_ = v___x_2240_;
                    v___y_2077_ = v___y_2228_;
                    v___y_2078_ = v___x_2243_;
                    v___y_2079_ = v___y_2229_;
                    v___y_2080_ = v___x_2245_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2052_);
                    v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2044_);
                    v___y_2064_ = v_currMacroScope_2234_;
                    v___y_2065_ = v___x_2236_;
                    v___y_2066_ = v___x_2239_;
                    v___y_2067_ = v___y_2232_;
                    v___y_2068_ = v_quotContext_2233_;
                    v___y_2069_ = v___x_2241_;
                    v___y_2070_ = v_id_2230_;
                    v___y_2071_ = v___y_2226_;
                    v___y_2072_ = v___x_2237_;
                    v___y_2073_ = v___y_2227_;
                    v___y_2074_ = v___x_2242_;
                    v___y_2075_ = v___x_2238_;
                    v___y_2076_ = v___x_2240_;
                    v___y_2077_ = v___y_2228_;
                    v___y_2078_ = v___x_2243_;
                    v___y_2079_ = v___y_2229_;
                    v___y_2080_ = v___x_2246_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2252_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__30;
                v___x_2253_ = l_Lean_Macro_throwErrorAt___redArg(
                    v_name_2053_,
                    v___x_2252_,
                    v___y_2061_,
                    v___y_2062_,
                );
                crate::leanh::lean_dec(v_name_2053_);
                if crate::leanh::lean_obj_tag(v___x_2253_) == 0 {
                    v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                    crate::leanh::lean_inc(v_a_2254_);
                    v_a_2255_ = crate::leanh::lean_ctor_get(v___x_2253_, 1);
                    crate::leanh::lean_inc(v_a_2255_);
                    crate::leanh::lean_dec_ref_known(v___x_2253_, 2);
                    v___y_2226_ = v___y_2248_;
                    v___y_2227_ = v___y_2249_;
                    v___y_2228_ = v___y_2250_;
                    v___y_2229_ = v___y_2251_;
                    v_id_2230_ = v_a_2254_;
                    v___y_2231_ = v___y_2061_;
                    v___y_2232_ = v_a_2255_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2251_);
                    crate::leanh::lean_dec(v___y_2250_);
                    crate::leanh::lean_dec(v___y_2249_);
                    crate::leanh::lean_dec(v___y_2248_);
                    crate::leanh::lean_dec(v___y_2052_);
                    crate::leanh::lean_dec(v___x_2050_);
                    crate::leanh::lean_dec_ref(v___x_2049_);
                    crate::leanh::lean_dec(v___x_2048_);
                    crate::leanh::lean_dec(v_fam_2047_);
                    crate::leanh::lean_dec_ref(v___x_2046_);
                    return v___x_2253_;
                }
            }
            4 => {
                crate::leanh::lean_inc_n(v___x_2256_, 2);
                crate::leanh::lean_inc(v_name_2053_);
                v___x_2259_ = l_Lake_Name_quoteFrom(v_name_2053_, v___x_2256_, v___y_2258_);
                crate::leanh::lean_inc(v___x_2055_);
                v___x_2260_ = l_Lake_Name_quoteFrom(v_ns_2054_, v___x_2055_, v___x_2056_);
                v___x_2261_ = l_Lean_Name_append(v___x_2055_, v___x_2256_);
                crate::leanh::lean_inc(v___x_2261_);
                v___x_2262_ = l_Lean_mkIdentFrom(v_tk_2057_, v___x_2261_, v___x_2056_);
                v___x_2263_ = l_Lake_Name_quoteFrom(v_tk_2057_, v___x_2261_, v___x_2051_);
                if crate::leanh::lean_obj_tag(v___y_2058_) == 1 {
                    crate::leanh::lean_dec(v___x_2256_);
                    crate::leanh::lean_dec(v_name_2053_);
                    v_val_2264_ = crate::leanh::lean_ctor_get(v___y_2058_, 0);
                    v___x_2265_ = l_Lean_Syntax_getArg(v_val_2264_, v___x_2044_);
                    v___x_2266_ = l_Lean_Syntax_getId(v___x_2265_);
                    v___x_2267_ = l_Lean_Name_append(v___x_2059_, v___x_2266_);
                    v___x_2268_ = l_Lean_mkIdentFrom(v___x_2265_, v___x_2267_, v___x_2056_);
                    crate::leanh::lean_dec(v___x_2265_);
                    v___y_2226_ = v___x_2259_;
                    v___y_2227_ = v___x_2262_;
                    v___y_2228_ = v___x_2260_;
                    v___y_2229_ = v___x_2263_;
                    v_id_2230_ = v___x_2268_;
                    v___y_2231_ = v___y_2061_;
                    v___y_2232_ = v___y_2062_;
                    state = 2;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2256_) == 1 {
                        v_pre_2269_ = crate::leanh::lean_ctor_get(v___x_2256_, 0);
                        crate::leanh::lean_inc(v_pre_2269_);
                        if crate::leanh::lean_obj_tag(v_pre_2269_) == 0 {
                            v_str_2270_ = crate::leanh::lean_ctor_get(v___x_2256_, 1);
                            crate::leanh::lean_inc_ref(v_str_2270_);
                            crate::leanh::lean_dec_ref_known(v___x_2256_, 2);
                            v___x_2271_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__31;
                            v___x_2272_ = lean_string_append(v_str_2270_, v___x_2271_);
                            v___x_2273_ = l_Lean_Name_str___override(v___x_2059_, v___x_2272_);
                            v___x_2274_ =
                                l_Lean_mkIdentFrom(v_name_2053_, v___x_2273_, v___x_2056_);
                            crate::leanh::lean_dec(v_name_2053_);
                            v___y_2226_ = v___x_2259_;
                            v___y_2227_ = v___x_2262_;
                            v___y_2228_ = v___x_2260_;
                            v___y_2229_ = v___x_2263_;
                            v_id_2230_ = v___x_2274_;
                            v___y_2231_ = v___y_2061_;
                            v___y_2232_ = v___y_2062_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2256_, 2);
                            crate::leanh::lean_dec(v_pre_2269_);
                            crate::leanh::lean_dec(v___x_2059_);
                            v___y_2248_ = v___x_2259_;
                            v___y_2249_ = v___x_2262_;
                            v___y_2250_ = v___x_2260_;
                            v___y_2251_ = v___x_2263_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2256_);
                        crate::leanh::lean_dec(v___x_2059_);
                        v___y_2248_ = v___x_2259_;
                        v___y_2249_ = v___x_2262_;
                        v___y_2250_ = v___x_2260_;
                        v___y_2251_ = v___x_2263_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2276_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2277_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_fam_2278_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2279_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2280_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2281_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2282_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2283_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_name_2284_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_ns_2285_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2286_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2287_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_tk_2288_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2289_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2290_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_____r_2291_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2292_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2293_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_12982__boxed_2294_: u8 = 0;
    let mut v___x_12985__boxed_2295_: u8 = 0;
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12982__boxed_2294_ = (crate::leanh::lean_unbox(v___x_2282_) as u8);
    v___x_12985__boxed_2295_ = (crate::leanh::lean_unbox(v___x_2287_) as u8);
    v_res_2296_ =
        l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(
            v___x_2275_,
            v___x_2276_,
            v___x_2277_,
            v_fam_2278_,
            v___x_2279_,
            v___x_2280_,
            v___x_2281_,
            v___x_12982__boxed_2294_,
            v___y_2283_,
            v_name_2284_,
            v_ns_2285_,
            v___x_2286_,
            v___x_12985__boxed_2295_,
            v_tk_2288_,
            v___y_2289_,
            v___x_2290_,
            v_____r_2291_,
            v___y_2292_,
            v___y_2293_,
        );
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec(v___x_2276_);
    crate::leanh::lean_dec(v___x_2275_);
    return v_res_2296_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(
    mut v_x_2304_: *mut crate::leanh::LeanObject,
    mut v_a_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut v_a_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ns_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v_fam_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2381_: u8 = 0;
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_a_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v___y_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2327_ = l_Lake_dataTypeDecl___closed__0;
                v___x_2328_ = l_Lake_builtinFacetCommand___closed__1;
                crate::leanh::lean_inc(v_x_2304_);
                v___x_2329_ = l_Lean_Syntax_isOfKind(v_x_2304_, v___x_2328_);
                if v___x_2329_ == 0 {
                    crate::leanh::lean_dec(v_x_2304_);
                    v___x_2330_ = crate::leanh::lean_box(1);
                    v___x_2331_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2331_, 0, v___x_2330_);
                    crate::leanh::lean_ctor_set(v___x_2331_, 1, v_a_2306_);
                    return v___x_2331_;
                } else {
                    v___x_2332_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2333_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2332_);
                    v___x_2334_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2335_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2334_);
                    v___x_2336_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2337_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2336_);
                    v___x_2338_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_name_2339_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2338_);
                    v___x_2340_ = crate::leanh::lean_unsigned_to_nat(5);
                    v_ns_2341_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2340_);
                    v___x_2342_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_2343_ = l_Lean_Syntax_getArg(v_x_2304_, v___x_2342_);
                    crate::leanh::lean_dec(v_x_2304_);
                    v___x_2414_ = l_Lean_Syntax_getOptional_x3f(v___x_2337_);
                    crate::leanh::lean_dec(v___x_2337_);
                    if crate::leanh::lean_obj_tag(v___x_2414_) == 0 {
                        v___x_2415_ = crate::leanh::lean_box(0);
                        v___y_2403_ = v___x_2415_;
                        state = 11;
                        continue;
                    } else {
                        v_val_2416_ = crate::leanh::lean_ctor_get(v___x_2414_, 0);
                        v_isSharedCheck_2423_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2414_)) as u8;
                        if v_isSharedCheck_2423_ == 0 {
                            v___x_2418_ = v___x_2414_;
                            v_isShared_2419_ = v_isSharedCheck_2423_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2416_);
                            crate::leanh::lean_dec(v___x_2414_);
                            v___x_2418_ = crate::leanh::lean_box(0);
                            v_isShared_2419_ = v_isSharedCheck_2423_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2308_) == 0 {
                    v_a_2309_ = crate::leanh::lean_ctor_get(v___y_2308_, 0);
                    v_a_2310_ = crate::leanh::lean_ctor_get(v___y_2308_, 1);
                    v_isSharedCheck_2317_ = (!crate::leanh::lean_is_exclusive(v___y_2308_)) as u8;
                    if v_isSharedCheck_2317_ == 0 {
                        v___x_2312_ = v___y_2308_;
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2310_);
                        crate::leanh::lean_inc(v_a_2309_);
                        crate::leanh::lean_dec(v___y_2308_);
                        v___x_2312_ = crate::leanh::lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2317_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2318_ = crate::leanh::lean_ctor_get(v___y_2308_, 0);
                    v_a_2319_ = crate::leanh::lean_ctor_get(v___y_2308_, 1);
                    v_isSharedCheck_2326_ = (!crate::leanh::lean_is_exclusive(v___y_2308_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___y_2308_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2319_);
                        crate::leanh::lean_inc(v_a_2318_);
                        crate::leanh::lean_dec(v___y_2308_);
                        v___x_2321_ = crate::leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2313_ == 0 {
                    v___x_2315_ = v___x_2312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2310_);
                    v___x_2315_ = v_reuseFailAlloc_2316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2315_;
            }
            4 => {
                if v_isShared_2322_ == 0 {
                    v___x_2324_ = v___x_2321_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_a_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2324_;
            }
            6 => {
                v_methods_2347_ = crate::leanh::lean_ctor_get(v_a_2305_, 0);
                v_quotContext_2348_ = crate::leanh::lean_ctor_get(v_a_2305_, 1);
                v_currMacroScope_2349_ = crate::leanh::lean_ctor_get(v_a_2305_, 2);
                v_currRecDepth_2350_ = crate::leanh::lean_ctor_get(v_a_2305_, 3);
                v_maxRecDepth_2351_ = crate::leanh::lean_ctor_get(v_a_2305_, 4);
                v_ref_2352_ = crate::leanh::lean_ctor_get(v_a_2305_, 5);
                v___x_2353_ = l_Lean_TSyntax_getId(v_ns_2341_);
                v_ref_2354_ = l_Lean_replaceRef(v_tk_2335_, v_ref_2352_);
                crate::leanh::lean_inc(v_maxRecDepth_2351_);
                crate::leanh::lean_inc(v_currRecDepth_2350_);
                crate::leanh::lean_inc(v_currMacroScope_2349_);
                crate::leanh::lean_inc(v_quotContext_2348_);
                crate::leanh::lean_inc(v_methods_2347_);
                v___x_2355_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2355_, 0, v_methods_2347_);
                crate::leanh::lean_ctor_set(v___x_2355_, 1, v_quotContext_2348_);
                crate::leanh::lean_ctor_set(v___x_2355_, 2, v_currMacroScope_2349_);
                crate::leanh::lean_ctor_set(v___x_2355_, 3, v_currRecDepth_2350_);
                crate::leanh::lean_ctor_set(v___x_2355_, 4, v_maxRecDepth_2351_);
                crate::leanh::lean_ctor_set(v___x_2355_, 5, v_ref_2354_);
                crate::leanh::lean_inc(v___x_2353_);
                v___x_2356_ = l_Lean_Macro_resolveNamespace(v___x_2353_, v___x_2355_, v_a_2306_);
                if crate::leanh::lean_obj_tag(v___x_2356_) == 0 {
                    v_a_2357_ = crate::leanh::lean_ctor_get(v___x_2356_, 0);
                    crate::leanh::lean_inc(v_a_2357_);
                    if crate::leanh::lean_obj_tag(v_a_2357_) == 1 {
                        v_a_2358_ = crate::leanh::lean_ctor_get(v___x_2356_, 1);
                        crate::leanh::lean_inc(v_a_2358_);
                        crate::leanh::lean_dec_ref_known(v___x_2356_, 2);
                        v_head_2359_ = crate::leanh::lean_ctor_get(v_a_2357_, 0);
                        crate::leanh::lean_inc(v_head_2359_);
                        crate::leanh::lean_dec_ref_known(v_a_2357_, 2);
                        v___x_2360_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0;
                        v___x_2361_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1;
                        v___x_2362_ = 0;
                        v_fam_2363_ = l_Lean_mkCIdentFrom(v_tk_2335_, v___x_2361_, v___x_2362_);
                        v___x_2364_ = l___private_Lake_Config_Kinds_0__Lake_facetKindForNamespace(
                            v_head_2359_,
                        );
                        crate::leanh::lean_dec(v_head_2359_);
                        v___x_2365_ = l_Lean_Name_isAnonymous(v___x_2364_);
                        if v___x_2365_ == 0 {
                            v___x_2366_ = crate::leanh::lean_box(0);
                            v___x_2367_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_2332_, v___x_2336_, v___x_2327_, v_fam_2363_, v___x_2343_, v___x_2360_, v___x_2361_, v___x_2362_, v___y_2346_, v_name_2339_, v_ns_2341_, v___x_2364_, v___x_2329_, v_tk_2335_, v___y_2345_, v___x_2353_, v___x_2366_, v___x_2355_, v_a_2358_);
                            crate::leanh::lean_dec_ref_known(v___x_2355_, 6);
                            crate::leanh::lean_dec(v___y_2345_);
                            v___y_2308_ = v___x_2367_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2368_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__2;
                            crate::leanh::lean_inc(v___x_2353_);
                            v___x_2369_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2353_,
                                    v___x_2365_,
                                );
                            v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
                            crate::leanh::lean_dec_ref(v___x_2369_);
                            v___x_2371_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3;
                            v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
                            v___x_2373_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_ns_2341_,
                                v___x_2372_,
                                v___x_2355_,
                                v_a_2358_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2373_) == 0 {
                                v_a_2374_ = crate::leanh::lean_ctor_get(v___x_2373_, 0);
                                crate::leanh::lean_inc(v_a_2374_);
                                v_a_2375_ = crate::leanh::lean_ctor_get(v___x_2373_, 1);
                                crate::leanh::lean_inc(v_a_2375_);
                                crate::leanh::lean_dec_ref_known(v___x_2373_, 2);
                                v___x_2376_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0(v___x_2332_, v___x_2336_, v___x_2327_, v_fam_2363_, v___x_2343_, v___x_2360_, v___x_2361_, v___x_2362_, v___y_2346_, v_name_2339_, v_ns_2341_, v___x_2364_, v___x_2329_, v_tk_2335_, v___y_2345_, v___x_2353_, v_a_2374_, v___x_2355_, v_a_2375_);
                                crate::leanh::lean_dec_ref_known(v___x_2355_, 6);
                                crate::leanh::lean_dec(v___y_2345_);
                                v___y_2308_ = v___x_2376_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2364_);
                                crate::leanh::lean_dec(v_fam_2363_);
                                crate::leanh::lean_dec_ref_known(v___x_2355_, 6);
                                crate::leanh::lean_dec(v___x_2353_);
                                crate::leanh::lean_dec(v___y_2346_);
                                crate::leanh::lean_dec(v___y_2345_);
                                crate::leanh::lean_dec(v___x_2343_);
                                crate::leanh::lean_dec(v_ns_2341_);
                                crate::leanh::lean_dec(v_name_2339_);
                                crate::leanh::lean_dec(v_tk_2335_);
                                v_a_2377_ = crate::leanh::lean_ctor_get(v___x_2373_, 0);
                                v_a_2378_ = crate::leanh::lean_ctor_get(v___x_2373_, 1);
                                v_isSharedCheck_2385_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2373_)) as u8;
                                if v_isSharedCheck_2385_ == 0 {
                                    v___x_2380_ = v___x_2373_;
                                    v_isShared_2381_ = v_isSharedCheck_2385_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2378_);
                                    crate::leanh::lean_inc(v_a_2377_);
                                    crate::leanh::lean_dec(v___x_2373_);
                                    v___x_2380_ = crate::leanh::lean_box(0);
                                    v_isShared_2381_ = v_isSharedCheck_2385_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2357_);
                        crate::leanh::lean_dec(v___y_2346_);
                        crate::leanh::lean_dec(v___y_2345_);
                        crate::leanh::lean_dec(v___x_2343_);
                        crate::leanh::lean_dec(v_name_2339_);
                        crate::leanh::lean_dec(v_tk_2335_);
                        v_a_2386_ = crate::leanh::lean_ctor_get(v___x_2356_, 1);
                        crate::leanh::lean_inc(v_a_2386_);
                        crate::leanh::lean_dec_ref_known(v___x_2356_, 2);
                        v___x_2387_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__4;
                        v___x_2388_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2353_,
                                v___x_2329_,
                            );
                        v___x_2389_ = lean_string_append(v___x_2387_, v___x_2388_);
                        crate::leanh::lean_dec_ref(v___x_2388_);
                        v___x_2390_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__3;
                        v___x_2391_ = lean_string_append(v___x_2389_, v___x_2390_);
                        v___x_2392_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_ns_2341_,
                            v___x_2391_,
                            v___x_2355_,
                            v_a_2386_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_2355_, 6);
                        crate::leanh::lean_dec(v_ns_2341_);
                        v___y_2308_ = v___x_2392_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2355_, 6);
                    crate::leanh::lean_dec(v___x_2353_);
                    crate::leanh::lean_dec(v___y_2346_);
                    crate::leanh::lean_dec(v___y_2345_);
                    crate::leanh::lean_dec(v___x_2343_);
                    crate::leanh::lean_dec(v_ns_2341_);
                    crate::leanh::lean_dec(v_name_2339_);
                    crate::leanh::lean_dec(v_tk_2335_);
                    v_a_2393_ = crate::leanh::lean_ctor_get(v___x_2356_, 0);
                    v_a_2394_ = crate::leanh::lean_ctor_get(v___x_2356_, 1);
                    v_isSharedCheck_2401_ = (!crate::leanh::lean_is_exclusive(v___x_2356_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v___x_2396_ = v___x_2356_;
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2394_);
                        crate::leanh::lean_inc(v_a_2393_);
                        crate::leanh::lean_dec(v___x_2356_);
                        v___x_2396_ = crate::leanh::lean_box(0);
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2381_ == 0 {
                    v___x_2383_ = v___x_2380_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2378_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2383_;
            }
            9 => {
                if v_isShared_2397_ == 0 {
                    v___x_2399_ = v___x_2396_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_a_2394_);
                    v___x_2399_ = v_reuseFailAlloc_2400_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2399_;
            }
            11 => {
                v___x_2404_ = l_Lean_Syntax_getOptional_x3f(v___x_2333_);
                crate::leanh::lean_dec(v___x_2333_);
                if crate::leanh::lean_obj_tag(v___x_2404_) == 0 {
                    v___x_2405_ = crate::leanh::lean_box(0);
                    v___y_2345_ = v___y_2403_;
                    v___y_2346_ = v___x_2405_;
                    state = 6;
                    continue;
                } else {
                    v_val_2406_ = crate::leanh::lean_ctor_get(v___x_2404_, 0);
                    v_isSharedCheck_2413_ = (!crate::leanh::lean_is_exclusive(v___x_2404_)) as u8;
                    if v_isSharedCheck_2413_ == 0 {
                        v___x_2408_ = v___x_2404_;
                        v_isShared_2409_ = v_isSharedCheck_2413_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2406_);
                        crate::leanh::lean_dec(v___x_2404_);
                        v___x_2408_ = crate::leanh::lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2413_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_2409_ == 0 {
                    v___x_2411_ = v___x_2408_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_val_2406_);
                    v___x_2411_ = v_reuseFailAlloc_2412_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2345_ = v___y_2403_;
                v___y_2346_ = v___x_2411_;
                state = 6;
                continue;
            }
            14 => {
                if v_isShared_2419_ == 0 {
                    v___x_2421_ = v___x_2418_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_val_2416_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_2403_ = v___x_2421_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___boxed(
    mut v_x_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2427_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1(
        v_x_2424_, v_a_2425_, v_a_2426_,
    );
    crate::leanh::lean_dec_ref(v_a_2425_);
    return v_res_2427_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(
    mut v_x_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v_fam_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kindLit_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nameLit_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetLit_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2640_: u8 = 0;
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2506_ = l_Lake_facetDataDecl___closed__1;
                crate::leanh::lean_inc(v_x_2503_);
                v___x_2507_ = l_Lean_Syntax_isOfKind(v_x_2503_, v___x_2506_);
                if v___x_2507_ == 0 {
                    crate::leanh::lean_dec(v_x_2503_);
                    v___x_2508_ = crate::leanh::lean_box(1);
                    v___x_2509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2509_, 0, v___x_2508_);
                    crate::leanh::lean_ctor_set(v___x_2509_, 1, v_a_2505_);
                    return v___x_2509_;
                } else {
                    v___x_2510_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2511_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2510_);
                    v___x_2512_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2513_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2512_);
                    v___x_2514_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_kind_2515_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2514_);
                    v___x_2516_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_name_2517_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2516_);
                    v___x_2518_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_2519_ = l_Lean_Syntax_getArg(v_x_2503_, v___x_2518_);
                    crate::leanh::lean_dec(v_x_2503_);
                    v___x_2635_ = l_Lean_Syntax_getOptional_x3f(v___x_2511_);
                    crate::leanh::lean_dec(v___x_2511_);
                    if crate::leanh::lean_obj_tag(v___x_2635_) == 0 {
                        v___x_2636_ = crate::leanh::lean_box(0);
                        v___y_2612_ = v___x_2636_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2637_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                        v_isSharedCheck_2644_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                        if v_isSharedCheck_2644_ == 0 {
                            v___x_2639_ = v___x_2635_;
                            v_isShared_2640_ = v_isSharedCheck_2644_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2637_);
                            crate::leanh::lean_dec(v___x_2635_);
                            v___x_2639_ = crate::leanh::lean_box(0);
                            v_isShared_2640_ = v_isSharedCheck_2644_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_2526_, 2);
                v___x_2535_ = l_Array_append___redArg(v___y_2526_, v___y_2534_);
                crate::leanh::lean_dec_ref(v___y_2534_);
                crate::leanh::lean_inc_n(v___y_2531_, 6);
                crate::leanh::lean_inc_n(v___y_2528_, 35);
                v___x_2536_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2536_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2536_, 1, v___y_2531_);
                crate::leanh::lean_ctor_set(v___x_2536_, 2, v___x_2535_);
                v___x_2537_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2538_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2538_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2538_, 1, v___x_2537_);
                v___x_2539_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2540_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2540_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2540_, 1, v___x_2539_);
                v___x_2541_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_2542_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2542_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2542_, 1, v___x_2541_);
                crate::leanh::lean_inc_n(v___x_2519_, 2);
                crate::leanh::lean_inc_ref(v___x_2542_);
                crate::leanh::lean_inc(v___y_2525_);
                crate::leanh::lean_inc_ref(v___x_2540_);
                crate::leanh::lean_inc(v___y_2521_);
                v___x_2543_ = l_Lean_Syntax_node8(
                    v___y_2528_,
                    v___y_2521_,
                    v___x_2536_,
                    v___x_2538_,
                    v___y_2532_,
                    v___x_2540_,
                    v___y_2522_,
                    v___y_2525_,
                    v___x_2542_,
                    v___x_2519_,
                );
                v___x_2544_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__7;
                v___x_2545_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__9;
                v___x_2546_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2546_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2546_, 1, v___y_2531_);
                crate::leanh::lean_ctor_set(v___x_2546_, 2, v___y_2526_);
                v___x_2547_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__10;
                v___x_2548_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__11;
                v___x_2549_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2549_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2549_, 1, v___x_2547_);
                v___x_2550_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2548_, v___x_2549_);
                v___x_2551_ = l_Lean_Syntax_node1(v___y_2528_, v___y_2531_, v___x_2550_);
                crate::leanh::lean_inc_ref_n(v___x_2546_, 12);
                v___x_2552_ = l_Lean_Syntax_node7(
                    v___y_2528_,
                    v___x_2545_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2551_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2546_,
                );
                v___x_2553_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__12;
                v___x_2554_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__13;
                v___x_2555_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__16;
                v___x_2556_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2555_, v___x_2546_);
                v___x_2557_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2557_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2553_);
                v___x_2558_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__18;
                v___x_2559_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__20;
                v___x_2560_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__22;
                v___x_2561_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__16);
                v___x_2562_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__17;
                crate::leanh::lean_inc_n(v___y_2523_, 3);
                crate::leanh::lean_inc_n(v___y_2530_, 3);
                v___x_2563_ = l_Lean_addMacroScope(v___y_2530_, v___x_2562_, v___y_2523_);
                v___x_2564_ = crate::leanh::lean_box(0);
                v___x_2565_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__4;
                v___x_2566_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2566_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2566_, 1, v___x_2561_);
                crate::leanh::lean_ctor_set(v___x_2566_, 2, v___x_2563_);
                crate::leanh::lean_ctor_set(v___x_2566_, 3, v___x_2565_);
                crate::leanh::lean_inc_ref_n(v___y_2524_, 2);
                v___x_2567_ = l_String_toRawSubstring_x27(v___y_2524_);
                v___x_2568_ = l_Lean_Name_mkStr1(v___y_2524_);
                v___x_2569_ = l_Lean_addMacroScope(v___y_2530_, v___x_2568_, v___y_2523_);
                v___x_2570_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2570_, 0, v___y_2529_);
                crate::leanh::lean_ctor_set(v___x_2570_, 1, v___x_2564_);
                v___x_2571_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2571_, 0, v___x_2570_);
                crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2564_);
                v___x_2572_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2572_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2572_, 1, v___x_2567_);
                crate::leanh::lean_ctor_set(v___x_2572_, 2, v___x_2569_);
                crate::leanh::lean_ctor_set(v___x_2572_, 3, v___x_2571_);
                v___x_2573_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__5;
                v___x_2574_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6;
                v___x_2575_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2576_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2576_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2576_, 1, v___x_2575_);
                v___x_2577_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_2579_ = crate::leanh::lean_box(0);
                v___x_2580_ = l_Lean_addMacroScope(v___y_2530_, v___x_2579_, v___y_2523_);
                v___x_2581_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__12;
                v___x_2582_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2582_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2582_, 1, v___x_2578_);
                crate::leanh::lean_ctor_set(v___x_2582_, 2, v___x_2580_);
                crate::leanh::lean_ctor_set(v___x_2582_, 3, v___x_2581_);
                v___x_2583_ = l_Lean_Syntax_node1(v___y_2528_, v___x_2577_, v___x_2582_);
                v___x_2584_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2574_, v___x_2576_, v___x_2583_);
                v___x_2585_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__26;
                v___x_2586_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__27;
                v___x_2587_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2587_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2587_, 1, v___x_2586_);
                v___x_2588_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2585_,
                    v___y_2527_,
                    v___x_2587_,
                    v___y_2533_,
                );
                v___x_2589_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_2590_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2590_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                crate::leanh::lean_inc_ref(v___x_2590_);
                crate::leanh::lean_inc(v___x_2584_);
                v___x_2591_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2573_,
                    v___x_2584_,
                    v___x_2588_,
                    v___x_2590_,
                );
                crate::leanh::lean_inc_ref(v___x_2572_);
                v___x_2592_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___y_2531_,
                    v___x_2572_,
                    v___x_2591_,
                    v___x_2519_,
                );
                crate::leanh::lean_inc_ref(v___x_2566_);
                v___x_2593_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2560_, v___x_2566_, v___x_2592_);
                v___x_2594_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2559_, v___x_2540_, v___x_2593_);
                v___x_2595_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2558_, v___x_2546_, v___x_2594_);
                v___x_2596_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__32;
                v___x_2597_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__29;
                v___x_2598_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__13;
                v___x_2599_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2599_, 0, v___y_2528_);
                crate::leanh::lean_ctor_set(v___x_2599_, 1, v___x_2597_);
                v___x_2600_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___y_2531_,
                    v___x_2572_,
                    v___y_2525_,
                    v___x_2519_,
                );
                v___x_2601_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2560_, v___x_2566_, v___x_2600_);
                v___x_2602_ = l_Lean_Syntax_node3(
                    v___y_2528_,
                    v___x_2573_,
                    v___x_2584_,
                    v___x_2601_,
                    v___x_2590_,
                );
                v___x_2603_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2598_, v___x_2599_, v___x_2602_);
                v___x_2604_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__64;
                v___x_2605_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2604_, v___x_2546_, v___x_2546_);
                v___x_2606_ = l_Lean_Syntax_node4(
                    v___y_2528_,
                    v___x_2596_,
                    v___x_2542_,
                    v___x_2603_,
                    v___x_2605_,
                    v___x_2546_,
                );
                v___x_2607_ = l_Lean_Syntax_node6(
                    v___y_2528_,
                    v___x_2554_,
                    v___x_2556_,
                    v___x_2557_,
                    v___x_2546_,
                    v___x_2546_,
                    v___x_2595_,
                    v___x_2606_,
                );
                v___x_2608_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___x_2544_, v___x_2552_, v___x_2607_);
                v___x_2609_ =
                    l_Lean_Syntax_node2(v___y_2528_, v___y_2531_, v___x_2543_, v___x_2608_);
                v___x_2610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                crate::leanh::lean_ctor_set(v___x_2610_, 1, v_a_2505_);
                return v___x_2610_;
            }
            2 => {
                v___x_2613_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__0;
                v___x_2614_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___closed__1;
                v___x_2615_ = 0;
                v_fam_2616_ = l_Lean_mkCIdentFrom(v_tk_2513_, v___x_2614_, v___x_2615_);
                v___x_2617_ = l_Lean_TSyntax_getId(v_kind_2515_);
                crate::leanh::lean_inc(v___x_2617_);
                v_kindLit_2618_ = l_Lake_Name_quoteFrom(v_kind_2515_, v___x_2617_, v___x_2615_);
                v___x_2619_ = l_Lean_TSyntax_getId(v_name_2517_);
                crate::leanh::lean_inc(v___x_2619_);
                v_nameLit_2620_ = l_Lake_Name_quoteFrom(v_name_2517_, v___x_2619_, v___x_2615_);
                v_quotContext_2621_ = crate::leanh::lean_ctor_get(v_a_2504_, 1);
                v_currMacroScope_2622_ = crate::leanh::lean_ctor_get(v_a_2504_, 2);
                v_ref_2623_ = crate::leanh::lean_ctor_get(v_a_2504_, 5);
                v_facet_2624_ = l_Lean_Name_append(v___x_2617_, v___x_2619_);
                crate::leanh::lean_inc(v_facet_2624_);
                crate::leanh::lean_inc(v_tk_2513_);
                v_facetLit_2625_ = l_Lake_Name_quoteFrom(v_tk_2513_, v_facet_2624_, v___x_2615_);
                v_id_2626_ = l_Lean_mkIdentFrom(v_tk_2513_, v_facet_2624_, v___x_2507_);
                v_ref_2627_ = l_Lean_replaceRef(v_tk_2513_, v_ref_2623_);
                crate::leanh::lean_dec(v_tk_2513_);
                v___x_2628_ = l_Lean_SourceInfo_fromRef(v_ref_2627_, v___x_2615_);
                crate::leanh::lean_dec(v_ref_2627_);
                v___x_2629_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2630_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_2631_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_2612_) == 1 {
                    v_val_2632_ = crate::leanh::lean_ctor_get(v___y_2612_, 0);
                    crate::leanh::lean_inc(v_val_2632_);
                    crate::leanh::lean_dec_ref_known(v___y_2612_, 1);
                    v___x_2633_ = l_Array_mkArray1___redArg(v_val_2632_);
                    v___y_2521_ = v___x_2630_;
                    v___y_2522_ = v_fam_2616_;
                    v___y_2523_ = v_currMacroScope_2622_;
                    v___y_2524_ = v___x_2613_;
                    v___y_2525_ = v_facetLit_2625_;
                    v___y_2526_ = v___x_2631_;
                    v___y_2527_ = v_kindLit_2618_;
                    v___y_2528_ = v___x_2628_;
                    v___y_2529_ = v___x_2614_;
                    v___y_2530_ = v_quotContext_2621_;
                    v___y_2531_ = v___x_2629_;
                    v___y_2532_ = v_id_2626_;
                    v___y_2533_ = v_nameLit_2620_;
                    v___y_2534_ = v___x_2633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2612_);
                    v___x_2634_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2521_ = v___x_2630_;
                    v___y_2522_ = v_fam_2616_;
                    v___y_2523_ = v_currMacroScope_2622_;
                    v___y_2524_ = v___x_2613_;
                    v___y_2525_ = v_facetLit_2625_;
                    v___y_2526_ = v___x_2631_;
                    v___y_2527_ = v_kindLit_2618_;
                    v___y_2528_ = v___x_2628_;
                    v___y_2529_ = v___x_2614_;
                    v___y_2530_ = v_quotContext_2621_;
                    v___y_2531_ = v___x_2629_;
                    v___y_2532_ = v_id_2626_;
                    v___y_2533_ = v_nameLit_2620_;
                    v___y_2534_ = v___x_2634_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2640_ == 0 {
                    v___x_2642_ = v___x_2639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_val_2637_);
                    v___x_2642_ = v_reuseFailAlloc_2643_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2612_ = v___x_2642_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___boxed(
    mut v_x_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1(
        v_x_2645_, v_a_2646_, v_a_2647_,
    );
    crate::leanh::lean_dec_ref(v_a_2646_);
    return v_res_2648_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(
    mut v_x_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: u8 = 0;
    let mut v___y_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2681_ = l_Lake_packageDataDecl___closed__1;
                crate::leanh::lean_inc(v_x_2678_);
                v___x_2682_ = l_Lean_Syntax_isOfKind(v_x_2678_, v___x_2681_);
                if v___x_2682_ == 0 {
                    crate::leanh::lean_dec(v_x_2678_);
                    v___x_2683_ = crate::leanh::lean_box(1);
                    v___x_2684_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
                    crate::leanh::lean_ctor_set(v___x_2684_, 1, v_a_2680_);
                    return v___x_2684_;
                } else {
                    v___x_2685_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2686_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2685_);
                    v___x_2687_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2688_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2687_);
                    v___x_2689_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2690_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2689_);
                    v___x_2691_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2692_ = l_Lean_Syntax_getArg(v_x_2678_, v___x_2691_);
                    crate::leanh::lean_dec(v_x_2678_);
                    v___x_2722_ = l_Lean_Syntax_getOptional_x3f(v___x_2686_);
                    crate::leanh::lean_dec(v___x_2686_);
                    if crate::leanh::lean_obj_tag(v___x_2722_) == 0 {
                        v___x_2723_ = crate::leanh::lean_box(0);
                        v___y_2712_ = v___x_2723_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2724_ = crate::leanh::lean_ctor_get(v___x_2722_, 0);
                        v_isSharedCheck_2731_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2722_)) as u8;
                        if v_isSharedCheck_2731_ == 0 {
                            v___x_2726_ = v___x_2722_;
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2724_);
                            crate::leanh::lean_dec(v___x_2722_);
                            v___x_2726_ = crate::leanh::lean_box(0);
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2697_);
                v___x_2700_ = l_Array_append___redArg(v___y_2697_, v___y_2699_);
                crate::leanh::lean_dec_ref(v___y_2699_);
                crate::leanh::lean_inc(v___y_2695_);
                crate::leanh::lean_inc_n(v___y_2698_, 2);
                v___x_2701_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2701_, 0, v___y_2698_);
                crate::leanh::lean_ctor_set(v___x_2701_, 1, v___y_2695_);
                crate::leanh::lean_ctor_set(v___x_2701_, 2, v___x_2700_);
                v___x_2702_ = l_Lean_SourceInfo_fromRef(v_tk_2688_, v___x_2682_);
                v___x_2703_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2704_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2702_);
                crate::leanh::lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                v___x_2705_ = l_Lake_Package_keyword;
                v___x_2706_ = l_Lean_mkIdentFrom(v_tk_2688_, v___x_2705_, v___y_2694_);
                crate::leanh::lean_dec(v_tk_2688_);
                v___x_2707_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2708_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2708_, 0, v___y_2698_);
                crate::leanh::lean_ctor_set(v___x_2708_, 1, v___x_2707_);
                crate::leanh::lean_inc(v___y_2696_);
                v___x_2709_ = l_Lean_Syntax_node6(
                    v___y_2698_,
                    v___y_2696_,
                    v___x_2701_,
                    v___x_2704_,
                    v___x_2706_,
                    v___x_2690_,
                    v___x_2708_,
                    v___x_2692_,
                );
                v___x_2710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
                crate::leanh::lean_ctor_set(v___x_2710_, 1, v_a_2680_);
                return v___x_2710_;
            }
            2 => {
                v_ref_2713_ = crate::leanh::lean_ctor_get(v_a_2679_, 5);
                v___x_2714_ = 0;
                v___x_2715_ = l_Lean_SourceInfo_fromRef(v_ref_2713_, v___x_2714_);
                v___x_2716_ = l_Lake_facetDataDecl___closed__1;
                v___x_2717_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_2712_) == 1 {
                    v_val_2719_ = crate::leanh::lean_ctor_get(v___y_2712_, 0);
                    crate::leanh::lean_inc(v_val_2719_);
                    crate::leanh::lean_dec_ref_known(v___y_2712_, 1);
                    v___x_2720_ = l_Array_mkArray1___redArg(v_val_2719_);
                    v___y_2694_ = v___x_2714_;
                    v___y_2695_ = v___x_2717_;
                    v___y_2696_ = v___x_2716_;
                    v___y_2697_ = v___x_2718_;
                    v___y_2698_ = v___x_2715_;
                    v___y_2699_ = v___x_2720_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2712_);
                    v___x_2721_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2694_ = v___x_2714_;
                    v___y_2695_ = v___x_2717_;
                    v___y_2696_ = v___x_2716_;
                    v___y_2697_ = v___x_2718_;
                    v___y_2698_ = v___x_2715_;
                    v___y_2699_ = v___x_2721_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2727_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_val_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2712_ = v___x_2729_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___boxed(
    mut v_x_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
    mut v_a_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1(
        v_x_2732_, v_a_2733_, v_a_2734_,
    );
    crate::leanh::lean_dec_ref(v_a_2733_);
    return v_res_2735_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(
    mut v_x_2764_: *mut crate::leanh::LeanObject,
    mut v_a_2765_: *mut crate::leanh::LeanObject,
    mut v_a_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: u8 = 0;
    let mut v___y_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = l_Lake_moduleDataDecl___closed__1;
                crate::leanh::lean_inc(v_x_2764_);
                v___x_2768_ = l_Lean_Syntax_isOfKind(v_x_2764_, v___x_2767_);
                if v___x_2768_ == 0 {
                    crate::leanh::lean_dec(v_x_2764_);
                    v___x_2769_ = crate::leanh::lean_box(1);
                    v___x_2770_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                    crate::leanh::lean_ctor_set(v___x_2770_, 1, v_a_2766_);
                    return v___x_2770_;
                } else {
                    v___x_2771_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2772_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2771_);
                    v___x_2773_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2774_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2773_);
                    v___x_2775_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2776_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2775_);
                    v___x_2777_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2778_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2777_);
                    crate::leanh::lean_dec(v_x_2764_);
                    v___x_2808_ = l_Lean_Syntax_getOptional_x3f(v___x_2772_);
                    crate::leanh::lean_dec(v___x_2772_);
                    if crate::leanh::lean_obj_tag(v___x_2808_) == 0 {
                        v___x_2809_ = crate::leanh::lean_box(0);
                        v___y_2798_ = v___x_2809_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2810_ = crate::leanh::lean_ctor_get(v___x_2808_, 0);
                        v_isSharedCheck_2817_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2808_)) as u8;
                        if v_isSharedCheck_2817_ == 0 {
                            v___x_2812_ = v___x_2808_;
                            v_isShared_2813_ = v_isSharedCheck_2817_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2810_);
                            crate::leanh::lean_dec(v___x_2808_);
                            v___x_2812_ = crate::leanh::lean_box(0);
                            v_isShared_2813_ = v_isSharedCheck_2817_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2783_);
                v___x_2786_ = l_Array_append___redArg(v___y_2783_, v___y_2785_);
                crate::leanh::lean_dec_ref(v___y_2785_);
                crate::leanh::lean_inc(v___y_2780_);
                crate::leanh::lean_inc_n(v___y_2781_, 2);
                v___x_2787_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2787_, 0, v___y_2781_);
                crate::leanh::lean_ctor_set(v___x_2787_, 1, v___y_2780_);
                crate::leanh::lean_ctor_set(v___x_2787_, 2, v___x_2786_);
                v___x_2788_ = l_Lean_SourceInfo_fromRef(v_tk_2774_, v___x_2768_);
                v___x_2789_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2790_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2790_, 0, v___x_2788_);
                crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                v___x_2791_ = l_Lake_Module_keyword;
                v___x_2792_ = l_Lean_mkIdentFrom(v_tk_2774_, v___x_2791_, v___y_2782_);
                crate::leanh::lean_dec(v_tk_2774_);
                v___x_2793_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2794_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2794_, 0, v___y_2781_);
                crate::leanh::lean_ctor_set(v___x_2794_, 1, v___x_2793_);
                crate::leanh::lean_inc(v___y_2784_);
                v___x_2795_ = l_Lean_Syntax_node6(
                    v___y_2781_,
                    v___y_2784_,
                    v___x_2787_,
                    v___x_2790_,
                    v___x_2792_,
                    v___x_2776_,
                    v___x_2794_,
                    v___x_2778_,
                );
                v___x_2796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2796_, 1, v_a_2766_);
                return v___x_2796_;
            }
            2 => {
                v_ref_2799_ = crate::leanh::lean_ctor_get(v_a_2765_, 5);
                v___x_2800_ = 0;
                v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2799_, v___x_2800_);
                v___x_2802_ = l_Lake_facetDataDecl___closed__1;
                v___x_2803_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_2798_) == 1 {
                    v_val_2805_ = crate::leanh::lean_ctor_get(v___y_2798_, 0);
                    crate::leanh::lean_inc(v_val_2805_);
                    crate::leanh::lean_dec_ref_known(v___y_2798_, 1);
                    v___x_2806_ = l_Array_mkArray1___redArg(v_val_2805_);
                    v___y_2780_ = v___x_2803_;
                    v___y_2781_ = v___x_2801_;
                    v___y_2782_ = v___x_2800_;
                    v___y_2783_ = v___x_2804_;
                    v___y_2784_ = v___x_2802_;
                    v___y_2785_ = v___x_2806_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2798_);
                    v___x_2807_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2780_ = v___x_2803_;
                    v___y_2781_ = v___x_2801_;
                    v___y_2782_ = v___x_2800_;
                    v___y_2783_ = v___x_2804_;
                    v___y_2784_ = v___x_2802_;
                    v___y_2785_ = v___x_2807_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_val_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2798_ = v___x_2815_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1___boxed(
    mut v_x_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
    mut v_a_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__moduleDataDecl__1(
        v_x_2818_, v_a_2819_, v_a_2820_,
    );
    crate::leanh::lean_dec_ref(v_a_2819_);
    return v_res_2821_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(
    mut v_x_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: u8 = 0;
    let mut v___y_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = l_Lake_libraryDataDecl___closed__1;
                crate::leanh::lean_inc(v_x_2853_);
                v___x_2857_ = l_Lean_Syntax_isOfKind(v_x_2853_, v___x_2856_);
                if v___x_2857_ == 0 {
                    crate::leanh::lean_dec(v_x_2853_);
                    v___x_2858_ = crate::leanh::lean_box(1);
                    v___x_2859_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2858_);
                    crate::leanh::lean_ctor_set(v___x_2859_, 1, v_a_2855_);
                    return v___x_2859_;
                } else {
                    v___x_2860_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2861_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2860_);
                    v___x_2862_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2863_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2862_);
                    v___x_2864_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2865_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2864_);
                    v___x_2866_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2867_ = l_Lean_Syntax_getArg(v_x_2853_, v___x_2866_);
                    crate::leanh::lean_dec(v_x_2853_);
                    v___x_2897_ = l_Lean_Syntax_getOptional_x3f(v___x_2861_);
                    crate::leanh::lean_dec(v___x_2861_);
                    if crate::leanh::lean_obj_tag(v___x_2897_) == 0 {
                        v___x_2898_ = crate::leanh::lean_box(0);
                        v___y_2887_ = v___x_2898_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2899_ = crate::leanh::lean_ctor_get(v___x_2897_, 0);
                        v_isSharedCheck_2906_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2897_)) as u8;
                        if v_isSharedCheck_2906_ == 0 {
                            v___x_2901_ = v___x_2897_;
                            v_isShared_2902_ = v_isSharedCheck_2906_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2899_);
                            crate::leanh::lean_dec(v___x_2897_);
                            v___x_2901_ = crate::leanh::lean_box(0);
                            v_isShared_2902_ = v_isSharedCheck_2906_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2872_);
                v___x_2875_ = l_Array_append___redArg(v___y_2872_, v___y_2874_);
                crate::leanh::lean_dec_ref(v___y_2874_);
                crate::leanh::lean_inc(v___y_2873_);
                crate::leanh::lean_inc_n(v___y_2871_, 2);
                v___x_2876_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2876_, 0, v___y_2871_);
                crate::leanh::lean_ctor_set(v___x_2876_, 1, v___y_2873_);
                crate::leanh::lean_ctor_set(v___x_2876_, 2, v___x_2875_);
                v___x_2877_ = l_Lean_SourceInfo_fromRef(v_tk_2863_, v___x_2857_);
                v___x_2878_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__packageDataDecl__1___closed__0;
                v___x_2879_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2877_);
                crate::leanh::lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                v___x_2880_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___closed__1;
                v___x_2881_ = l_Lean_mkIdentFrom(v_tk_2863_, v___x_2880_, v___y_2869_);
                crate::leanh::lean_dec(v_tk_2863_);
                v___x_2882_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2883_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2883_, 0, v___y_2871_);
                crate::leanh::lean_ctor_set(v___x_2883_, 1, v___x_2882_);
                crate::leanh::lean_inc(v___y_2870_);
                v___x_2884_ = l_Lean_Syntax_node6(
                    v___y_2871_,
                    v___y_2870_,
                    v___x_2876_,
                    v___x_2879_,
                    v___x_2881_,
                    v___x_2865_,
                    v___x_2883_,
                    v___x_2867_,
                );
                v___x_2885_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2885_, 0, v___x_2884_);
                crate::leanh::lean_ctor_set(v___x_2885_, 1, v_a_2855_);
                return v___x_2885_;
            }
            2 => {
                v_ref_2888_ = crate::leanh::lean_ctor_get(v_a_2854_, 5);
                v___x_2889_ = 0;
                v___x_2890_ = l_Lean_SourceInfo_fromRef(v_ref_2888_, v___x_2889_);
                v___x_2891_ = l_Lake_facetDataDecl___closed__1;
                v___x_2892_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_2893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_2887_) == 1 {
                    v_val_2894_ = crate::leanh::lean_ctor_get(v___y_2887_, 0);
                    crate::leanh::lean_inc(v_val_2894_);
                    crate::leanh::lean_dec_ref_known(v___y_2887_, 1);
                    v___x_2895_ = l_Array_mkArray1___redArg(v_val_2894_);
                    v___y_2869_ = v___x_2889_;
                    v___y_2870_ = v___x_2891_;
                    v___y_2871_ = v___x_2890_;
                    v___y_2872_ = v___x_2893_;
                    v___y_2873_ = v___x_2892_;
                    v___y_2874_ = v___x_2895_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2887_);
                    v___x_2896_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2869_ = v___x_2889_;
                    v___y_2870_ = v___x_2891_;
                    v___y_2871_ = v___x_2890_;
                    v___y_2872_ = v___x_2893_;
                    v___y_2873_ = v___x_2892_;
                    v___y_2874_ = v___x_2896_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2902_ == 0 {
                    v___x_2904_ = v___x_2901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_val_2899_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2887_ = v___x_2904_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1___boxed(
    mut v_x_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2910_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__libraryDataDecl__1(
        v_x_2907_, v_a_2908_, v_a_2909_,
    );
    crate::leanh::lean_dec_ref(v_a_2908_);
    return v_res_2910_;
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(
    mut v_x_2959_: *mut crate::leanh::LeanObject,
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tgt_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2962_ = l_Lake_customDataDecl___closed__1;
                crate::leanh::lean_inc(v_x_2959_);
                v___x_2963_ = l_Lean_Syntax_isOfKind(v_x_2959_, v___x_2962_);
                if v___x_2963_ == 0 {
                    crate::leanh::lean_dec(v_x_2959_);
                    v___x_2964_ = crate::leanh::lean_box(1);
                    v___x_2965_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2964_);
                    crate::leanh::lean_ctor_set(v___x_2965_, 1, v_a_2961_);
                    return v___x_2965_;
                } else {
                    v___x_2966_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2967_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2966_);
                    v___x_2968_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_tk_2969_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2968_);
                    v___x_2970_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_pkg_2971_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2970_);
                    v___x_2972_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_tgt_2973_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2972_);
                    v___x_2974_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_2975_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2974_);
                    crate::leanh::lean_dec(v_x_2959_);
                    v___x_3039_ = l_Lean_Syntax_getOptional_x3f(v___x_2967_);
                    crate::leanh::lean_dec(v___x_2967_);
                    if crate::leanh::lean_obj_tag(v___x_3039_) == 0 {
                        v___x_3040_ = crate::leanh::lean_box(0);
                        v___y_3018_ = v___x_3040_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3041_ = crate::leanh::lean_ctor_get(v___x_3039_, 0);
                        v_isSharedCheck_3048_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3039_)) as u8;
                        if v_isSharedCheck_3048_ == 0 {
                            v___x_3043_ = v___x_3039_;
                            v_isShared_3044_ = v_isSharedCheck_3048_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3041_);
                            crate::leanh::lean_dec(v___x_3039_);
                            v___x_3043_ = crate::leanh::lean_box(0);
                            v_isShared_3044_ = v_isSharedCheck_3048_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2977_);
                v___x_2988_ = l_Array_append___redArg(v___y_2977_, v___y_2987_);
                crate::leanh::lean_dec_ref(v___y_2987_);
                crate::leanh::lean_inc_n(v___y_2978_, 3);
                crate::leanh::lean_inc_n(v___y_2981_, 13);
                v___x_2989_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2989_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_2989_, 1, v___y_2978_);
                crate::leanh::lean_ctor_set(v___x_2989_, 2, v___x_2988_);
                v___x_2990_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__0;
                v___x_2991_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2991_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                v___x_2992_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__1;
                v___x_2993_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2993_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_2993_, 1, v___x_2992_);
                v___x_2994_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__1;
                v___x_2995_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__facetDataDecl__1___closed__6;
                v___x_2996_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__20;
                v___x_2997_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2997_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_2997_, 1, v___x_2996_);
                v___x_2998_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__22;
                v___x_2999_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__24);
                v___x_3000_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_2986_);
                crate::leanh::lean_inc(v___y_2984_);
                v___x_3001_ = l_Lean_addMacroScope(v___y_2984_, v___x_3000_, v___y_2986_);
                v___x_3002_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__3;
                v___x_3003_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3003_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_3003_, 1, v___x_2999_);
                crate::leanh::lean_ctor_set(v___x_3003_, 2, v___x_3001_);
                crate::leanh::lean_ctor_set(v___x_3003_, 3, v___x_3002_);
                v___x_3004_ = l_Lean_Syntax_node1(v___y_2981_, v___x_2998_, v___x_3003_);
                v___x_3005_ =
                    l_Lean_Syntax_node2(v___y_2981_, v___x_2995_, v___x_2997_, v___x_3004_);
                v___x_3006_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__36;
                v___x_3007_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3007_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_3007_, 1, v___x_3006_);
                v___x_3008_ = l_Lean_Syntax_node1(v___y_2981_, v___y_2978_, v___y_2982_);
                v___x_3009_ = l_Lean_Syntax_node3(
                    v___y_2981_,
                    v___y_2978_,
                    v___y_2985_,
                    v___x_3007_,
                    v___x_3008_,
                );
                v___x_3010_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__builtinFacetCommand__1___lam__0___closed__28;
                v___x_3011_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3011_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_3011_, 1, v___x_3010_);
                v___x_3012_ = l_Lean_Syntax_node3(
                    v___y_2981_,
                    v___x_2994_,
                    v___x_3005_,
                    v___x_3009_,
                    v___x_3011_,
                );
                v___x_3013_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__2;
                v___x_3014_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3014_, 0, v___y_2981_);
                crate::leanh::lean_ctor_set(v___x_3014_, 1, v___x_3013_);
                crate::leanh::lean_inc(v___y_2983_);
                v___x_3015_ = l_Lean_Syntax_node8(
                    v___y_2981_,
                    v___y_2983_,
                    v___x_2989_,
                    v___x_2991_,
                    v___y_2979_,
                    v___x_2993_,
                    v___y_2980_,
                    v___x_3012_,
                    v___x_3014_,
                    v___x_2975_,
                );
                v___x_3016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3016_, 0, v___x_3015_);
                crate::leanh::lean_ctor_set(v___x_3016_, 1, v_a_2961_);
                return v___x_3016_;
            }
            2 => {
                v_quotContext_3019_ = crate::leanh::lean_ctor_get(v_a_2960_, 1);
                v_currMacroScope_3020_ = crate::leanh::lean_ctor_get(v_a_2960_, 2);
                v_ref_3021_ = crate::leanh::lean_ctor_get(v_a_2960_, 5);
                v_ref_3022_ = l_Lean_replaceRef(v_tk_2969_, v_ref_3021_);
                crate::leanh::lean_dec(v_tk_2969_);
                v___x_3023_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___closed__5;
                v___x_3024_ = 0;
                v___x_3025_ = l_Lean_mkCIdentFrom(v_ref_3022_, v___x_3023_, v___x_3024_);
                v___x_3026_ = l_Lean_TSyntax_getId(v_pkg_2971_);
                v___x_3027_ = l_Lean_TSyntax_getId(v_tgt_2973_);
                crate::leanh::lean_inc(v___x_3027_);
                crate::leanh::lean_inc(v___x_3026_);
                v___x_3028_ = l_Lean_Name_append(v___x_3026_, v___x_3027_);
                v___x_3029_ = l_Lean_mkIdentFrom(v_tgt_2973_, v___x_3028_, v___x_3024_);
                crate::leanh::lean_dec(v_tgt_2973_);
                v___x_3030_ = l_Lake_Name_quoteFrom(v_pkg_2971_, v___x_3026_, v___x_3024_);
                crate::leanh::lean_inc(v___x_3030_);
                v___x_3031_ = l_Lake_Name_quoteFrom(v___x_3030_, v___x_3027_, v___x_3024_);
                v___x_3032_ = l_Lean_SourceInfo_fromRef(v_ref_3022_, v___x_3024_);
                crate::leanh::lean_dec(v_ref_3022_);
                v___x_3033_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__70;
                v___x_3034_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__68;
                v___x_3035_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71), core::ptr::addr_of_mut!(l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71_once), _init_l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__71);
                if crate::leanh::lean_obj_tag(v___y_3018_) == 1 {
                    v_val_3036_ = crate::leanh::lean_ctor_get(v___y_3018_, 0);
                    crate::leanh::lean_inc(v_val_3036_);
                    crate::leanh::lean_dec_ref_known(v___y_3018_, 1);
                    v___x_3037_ = l_Array_mkArray1___redArg(v_val_3036_);
                    v___y_2977_ = v___x_3035_;
                    v___y_2978_ = v___x_3034_;
                    v___y_2979_ = v___x_3029_;
                    v___y_2980_ = v___x_3025_;
                    v___y_2981_ = v___x_3032_;
                    v___y_2982_ = v___x_3031_;
                    v___y_2983_ = v___x_3033_;
                    v___y_2984_ = v_quotContext_3019_;
                    v___y_2985_ = v___x_3030_;
                    v___y_2986_ = v_currMacroScope_3020_;
                    v___y_2987_ = v___x_3037_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3018_);
                    v___x_3038_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__dataTypeDecl__1___closed__72;
                    v___y_2977_ = v___x_3035_;
                    v___y_2978_ = v___x_3034_;
                    v___y_2979_ = v___x_3029_;
                    v___y_2980_ = v___x_3025_;
                    v___y_2981_ = v___x_3032_;
                    v___y_2982_ = v___x_3031_;
                    v___y_2983_ = v___x_3033_;
                    v___y_2984_ = v_quotContext_3019_;
                    v___y_2985_ = v___x_3030_;
                    v___y_2986_ = v_currMacroScope_3020_;
                    v___y_2987_ = v___x_3038_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3044_ == 0 {
                    v___x_3046_ = v___x_3043_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_val_3041_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3018_ = v___x_3046_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1___boxed(
    mut v_x_3049_: *mut crate::leanh::LeanObject,
    mut v_a_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Lake___aux__Lake__Build__Data______macroRules__Lake__customDataDecl__1(
        v_x_3049_, v_a_3050_, v_a_3051_,
    );
    crate::leanh::lean_dec_ref(v_a_3050_);
    return v_res_3052_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Data(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Data(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Data(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Kinds(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Data(builtin);
}

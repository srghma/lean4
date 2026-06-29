// Lean compiler output
// Module: Lean.Elab.AuxDef
// Imports: Lean.Elab.Command
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_replacePrefix, l_Lean_Syntax_isNone, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr4,
    l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7,
    lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_DeclNameGenerator_mkUniqueName, l_Lean_DeclNameGenerator_ofPrefix,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_components;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_getCurrMacroScope___redArg,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Environment::{l_Lean_Environment_header, l_Lean_Environment_setExporting};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l_Lean_Elab_Command_aux__def___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 117, 120, 95, 100, 101, 102, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_aux__def___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11510100434945111860 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16981400742628996529 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_aux__def___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__3_value)
                as *mut crate::leanh::LeanObject,
            6797826372810318163 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Elab_Command_aux__def___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__7_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Elab_Command_aux__def___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__7_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__9_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lean_Elab_Command_aux__def___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__9_value)
                as *mut crate::leanh::LeanObject,
            3961966953292576997 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__11_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__13_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__14_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__15_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_aux__def___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_aux__def___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__15_value)
                as *mut crate::leanh::LeanObject,
            2533412339571800130 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__17_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__20_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lean_Elab_Command_aux__def___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__21_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__20_value)
                as *mut crate::leanh::LeanObject,
            18370519569176055110 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__22_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__24_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__25_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__23_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__26_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Lean_Elab_Command_aux__def___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__27_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__26_value)
                as *mut crate::leanh::LeanObject,
            17243740965612849207 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__28_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lean_Elab_Command_aux__def___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_aux__def___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__29_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_aux__def___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__29_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_aux__def___closed__29_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__29_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__28_value)
                as *mut crate::leanh::LeanObject,
            14884320544314593060 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__30_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__29_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__31_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__27_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__32_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__25_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__31_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__33_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_aux__def___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__34_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__33_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__35_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__32_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__34_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__36_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_aux__def___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__37_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__36_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__38_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__37_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__39_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__35_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__38_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__40_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_aux__def___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__41_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__40_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__42_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__39_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__41_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__43_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__42_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__38_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_aux__def___closed__44_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__43_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_aux__def___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Command_aux__def: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__44_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabAuxDef___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 101, 116, 97, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__1_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [100, 101, 102, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__3_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [100, 101, 99, 108, 73, 100, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__4_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__5_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__6_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__7_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__8_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 117, 102, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__9_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_Command_elabAuxDef___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__10_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__11_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__12_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__12_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabAuxDef___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabAuxDef___closed__15_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [95, 97, 117, 120, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__15_value)
                as *mut crate::leanh::LeanObject,
            10888182157725215727 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__17_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabAuxDef___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__17_value)
                as *mut crate::leanh::LeanObject,
            13286986945483979944 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabAuxDef___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__19_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__9_value)
                as *mut crate::leanh::LeanObject,
            9063780239635860524 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabAuxDef___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabAuxDef___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 65, 117, 120, 68, 101, 102, 0]};
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__1_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_aux__def___closed__2_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__0_value) as *mut crate::leanh::LeanObject,2325054892682580979 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = crate::leanh::lean_box(0);
    v___x_607_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_608_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_608_, 0, v___x_607_);
    crate::leanh::lean_ctor_set(v___x_608_, 1, v___x_606_);
    return v___x_608_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___closed__0);
    v___x_611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_611_, 0, v___x_610_);
    return v___x_611_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg___boxed(
    mut v___y_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_613_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
    return v_res_613_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(
    mut v_00_u03b1_614_: *mut crate::leanh::LeanObject,
    mut v___y_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
    return v___x_618_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___boxed(
    mut v_00_u03b1_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
    mut v___y_621_: *mut crate::leanh::LeanObject,
    mut v___y_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_623_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0(
        v_00_u03b1_619_,
        v___y_620_,
        v___y_621_,
    );
    crate::leanh::lean_dec(v___y_621_);
    crate::leanh::lean_dec_ref(v___y_620_);
    return v_res_623_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(
    mut v___y_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = lean_st_ref_get(v___y_624_);
    v_env_627_ = crate::leanh::lean_ctor_get(v___x_626_, 0);
    crate::leanh::lean_inc_ref(v_env_627_);
    crate::leanh::lean_dec(v___x_626_);
    v___x_628_ = l_Lean_Environment_header(v_env_627_);
    crate::leanh::lean_dec_ref(v_env_627_);
    v_mainModule_629_ = crate::leanh::lean_ctor_get(v___x_628_, 0);
    crate::leanh::lean_inc(v_mainModule_629_);
    crate::leanh::lean_dec_ref(v___x_628_);
    v___x_630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_630_, 0, v_mainModule_629_);
    return v___x_630_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg___boxed(
    mut v___y_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_633_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_631_);
    crate::leanh::lean_dec(v___y_631_);
    return v_res_633_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(
    mut v___y_634_: *mut crate::leanh::LeanObject,
    mut v___y_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_635_);
    return v___x_637_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___boxed(
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1(v___y_638_, v___y_639_);
    crate::leanh::lean_dec(v___y_639_);
    crate::leanh::lean_dec_ref(v___y_638_);
    return v_res_641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(
    mut v_sz_642_: usize,
    mut v_i_643_: usize,
    mut v_bs_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_645_: u8 = 0;
    let mut v_v_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: usize = 0;
    let mut v___x_652_: usize = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_645_ = lean_usize_dec_lt(v_i_643_, v_sz_642_);
                if v___x_645_ == 0 {
                    return v_bs_644_;
                } else {
                    v_v_646_ = lean_array_uget(v_bs_644_, v_i_643_);
                    v___x_647_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_648_ = lean_array_uset(v_bs_644_, v_i_643_, v___x_647_);
                    v___x_649_ = l_Lean_TSyntax_getId(v_v_646_);
                    crate::leanh::lean_dec(v_v_646_);
                    v___x_650_ = lean_erase_macro_scopes(v___x_649_);
                    v___x_651_ = 1usize;
                    v___x_652_ = lean_usize_add(v_i_643_, v___x_651_);
                    v___x_653_ = lean_array_uset(v_bs_x27_648_, v_i_643_, v___x_650_);
                    v_i_643_ = v___x_652_;
                    v_bs_644_ = v___x_653_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3___boxed(
    mut v_sz_655_: *mut crate::leanh::LeanObject,
    mut v_i_656_: *mut crate::leanh::LeanObject,
    mut v_bs_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_658_: usize = 0;
    let mut v_i_boxed_659_: usize = 0;
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_658_ = crate::leanh::lean_unbox_usize(v_sz_655_);
    crate::leanh::lean_dec(v_sz_655_);
    v_i_boxed_659_ = crate::leanh::lean_unbox_usize(v_i_656_);
    crate::leanh::lean_dec(v_i_656_);
    v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_boxed_658_, v_i_boxed_659_, v_bs_657_);
    return v_res_660_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(
    mut v_as_661_: *mut crate::leanh::LeanObject,
    mut v_i_662_: usize,
    mut v_stop_663_: usize,
    mut v_b_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_665_: u8 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_665_ = lean_usize_dec_eq(v_i_662_, v_stop_663_);
                if v___x_665_ == 0 {
                    v___x_666_ = lean_array_uget_borrowed(v_as_661_, v_i_662_);
                    crate::leanh::lean_inc(v___x_666_);
                    v___x_667_ = l_Lean_Name_append(v_b_664_, v___x_666_);
                    v___x_668_ = 1usize;
                    v___x_669_ = lean_usize_add(v_i_662_, v___x_668_);
                    v_i_662_ = v___x_669_;
                    v_b_664_ = v___x_667_;
                    state = 0;
                    continue;
                } else {
                    return v_b_664_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4___boxed(
    mut v_as_671_: *mut crate::leanh::LeanObject,
    mut v_i_672_: *mut crate::leanh::LeanObject,
    mut v_stop_673_: *mut crate::leanh::LeanObject,
    mut v_b_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_675_: usize = 0;
    let mut v_stop_boxed_676_: usize = 0;
    let mut v_res_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_675_ = crate::leanh::lean_unbox_usize(v_i_672_);
    crate::leanh::lean_dec(v_i_672_);
    v_stop_boxed_676_ = crate::leanh::lean_unbox_usize(v_stop_673_);
    crate::leanh::lean_dec(v_stop_673_);
    v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v_as_671_, v_i_boxed_675_, v_stop_boxed_676_, v_b_674_);
    crate::leanh::lean_dec_ref(v_as_671_);
    return v_res_677_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(
    mut v_a_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_685_: u8 = 0;
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_678_) == 0 {
                    v___x_680_ = l_List_reverse___redArg(v_a_679_);
                    return v___x_680_;
                } else {
                    v_head_681_ = crate::leanh::lean_ctor_get(v_a_678_, 0);
                    v_tail_682_ = crate::leanh::lean_ctor_get(v_a_678_, 1);
                    v_isSharedCheck_692_ = (!crate::leanh::lean_is_exclusive(v_a_678_)) as u8;
                    if v_isSharedCheck_692_ == 0 {
                        v___x_684_ = v_a_678_;
                        v_isShared_685_ = v_isSharedCheck_692_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_682_);
                        crate::leanh::lean_inc(v_head_681_);
                        crate::leanh::lean_dec(v_a_678_);
                        v___x_684_ = crate::leanh::lean_box(0);
                        v_isShared_685_ = v_isSharedCheck_692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_686_ = 0;
                v___x_687_ = l_Lean_Name_toString(v_head_681_, v___x_686_);
                if v_isShared_685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_684_, 1, v_a_679_);
                    crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_687_);
                    v___x_689_ = v___x_684_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 1, v_a_679_);
                    v___x_689_ = v_reuseFailAlloc_691_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_678_ = v_tail_682_;
                v_a_679_ = v___x_689_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Command_elabAuxDef___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_709_;
}
pub unsafe fn l_Lean_Elab_Command_elabAuxDef(
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: u8 = 0;
    let mut v___y_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v_a_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_884_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut v_a_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_892_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_896_: u8 = 0;
    let mut v___y_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suggestion_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_913_: usize = 0;
    let mut v___x_914_: usize = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: u8 = 0;
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: usize = 0;
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_725_ = l_Lean_Elab_Command_aux__def___closed__0;
                v___x_726_ = l_Lean_Elab_Command_aux__def___closed__2;
                v___x_727_ = l_Lean_Elab_Command_aux__def___closed__4;
                crate::leanh::lean_inc(v_x_721_);
                v___x_728_ = l_Lean_Syntax_isOfKind(v_x_721_, v___x_727_);
                if v___x_728_ == 0 {
                    crate::leanh::lean_dec(v_x_721_);
                    v___x_787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
                    return v___x_787_;
                } else {
                    v___x_788_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_938_ = l_Lean_Syntax_getArg(v_x_721_, v___x_788_);
                    v___x_939_ = l_Lean_Syntax_isNone(v___x_938_);
                    if v___x_939_ == 0 {
                        v___x_940_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_938_);
                        v___x_941_ = l_Lean_Syntax_matchesNull(v___x_938_, v___x_940_);
                        if v___x_941_ == 0 {
                            crate::leanh::lean_dec(v___x_938_);
                            crate::leanh::lean_dec(v_x_721_);
                            v___x_942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
                            return v___x_942_;
                        } else {
                            v_doc_x3f_943_ = l_Lean_Syntax_getArg(v___x_938_, v___x_788_);
                            crate::leanh::lean_dec(v___x_938_);
                            v___x_944_ = l_Lean_Elab_Command_elabAuxDef___closed__19;
                            crate::leanh::lean_inc(v_doc_x3f_943_);
                            v___x_945_ = l_Lean_Syntax_isOfKind(v_doc_x3f_943_, v___x_944_);
                            if v___x_945_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_943_);
                                crate::leanh::lean_dec(v_x_721_);
                                v___x_946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
                                return v___x_946_;
                            } else {
                                v___x_947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_947_, 0, v_doc_x3f_943_);
                                v_doc_x3f_924_ = v___x_947_;
                                v___y_925_ = v_a_722_;
                                v___y_926_ = v_a_723_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_938_);
                        v___x_948_ = crate::leanh::lean_box(0);
                        v_doc_x3f_924_ = v___x_948_;
                        v___y_925_ = v_a_722_;
                        v___y_926_ = v_a_723_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_743_, 2);
                v___x_745_ = l_Array_append___redArg(v___y_743_, v___y_744_);
                crate::leanh::lean_dec_ref(v___y_744_);
                crate::leanh::lean_inc_n(v___y_741_, 6);
                crate::leanh::lean_inc_n(v___y_733_, 17);
                v___x_746_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_746_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_746_, 1, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_746_, 2, v___x_745_);
                v___x_747_ = l_Lean_Syntax_node1(v___y_733_, v___y_741_, v___y_742_);
                v___x_748_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_748_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_748_, 1, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_748_, 2, v___y_743_);
                v___x_749_ = l_Lean_Elab_Command_elabAuxDef___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_738_, 7);
                v___x_750_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_726_, v___x_749_);
                v___x_751_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_751_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_749_);
                v___x_752_ = l_Lean_Syntax_node1(v___y_733_, v___x_750_, v___x_751_);
                v___x_753_ = l_Lean_Syntax_node1(v___y_733_, v___y_741_, v___x_752_);
                crate::leanh::lean_inc_ref_n(v___x_748_, 8);
                v___x_754_ = l_Lean_Syntax_node7(
                    v___y_733_, v___y_732_, v___y_737_, v___x_746_, v___x_747_, v___x_748_,
                    v___x_753_, v___x_748_, v___x_748_,
                );
                v___x_755_ = l_Lean_Elab_Command_elabAuxDef___closed__1;
                v___x_756_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_726_, v___x_755_);
                v___x_757_ = l_Lean_Elab_Command_elabAuxDef___closed__2;
                v___x_758_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_758_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_758_, 1, v___x_757_);
                v___x_759_ = l_Lean_Elab_Command_elabAuxDef___closed__3;
                v___x_760_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_726_, v___x_759_);
                v___x_761_ = crate::leanh::lean_box(2);
                v___x_762_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_762_, 0, v___x_761_);
                crate::leanh::lean_ctor_set(v___x_762_, 1, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_762_, 2, v___y_730_);
                v___x_763_ = l_Lean_mkIdentFrom(v___x_762_, v___y_731_, v___x_728_);
                crate::leanh::lean_dec_ref_known(v___x_762_, 3);
                v___x_764_ = l_Lean_Syntax_node2(v___y_733_, v___x_760_, v___x_763_, v___x_748_);
                v___x_765_ = l_Lean_Elab_Command_elabAuxDef___closed__4;
                v___x_766_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_726_, v___x_765_);
                v___x_767_ = l_Lean_Elab_Command_aux__def___closed__14;
                v___x_768_ = l_Lean_Elab_Command_elabAuxDef___closed__5;
                v___x_769_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_767_, v___x_768_);
                v___x_770_ = l_Lean_Elab_Command_aux__def___closed__33;
                v___x_771_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_771_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_770_);
                v___x_772_ = l_Lean_Syntax_node2(v___y_733_, v___x_769_, v___x_771_, v___y_736_);
                v___x_773_ = l_Lean_Syntax_node1(v___y_733_, v___y_741_, v___x_772_);
                v___x_774_ = l_Lean_Syntax_node2(v___y_733_, v___x_766_, v___x_748_, v___x_773_);
                v___x_775_ = l_Lean_Elab_Command_elabAuxDef___closed__6;
                v___x_776_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_726_, v___x_775_);
                v___x_777_ = l_Lean_Elab_Command_aux__def___closed__40;
                v___x_778_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_778_, 0, v___y_733_);
                crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = l_Lean_Elab_Command_elabAuxDef___closed__7;
                v___x_780_ = l_Lean_Elab_Command_elabAuxDef___closed__8;
                v___x_781_ = l_Lean_Name_mkStr4(v___x_725_, v___y_738_, v___x_779_, v___x_780_);
                v___x_782_ = l_Lean_Syntax_node2(v___y_733_, v___x_781_, v___x_748_, v___x_748_);
                v___x_783_ = l_Lean_Syntax_node4(
                    v___y_733_, v___x_776_, v___x_778_, v___y_740_, v___x_782_, v___x_748_,
                );
                v___x_784_ = l_Lean_Syntax_node5(
                    v___y_733_, v___x_756_, v___x_758_, v___x_764_, v___x_774_, v___x_783_,
                    v___x_748_,
                );
                v___x_785_ = l_Lean_Syntax_node2(v___y_733_, v___y_739_, v___x_754_, v___x_784_);
                v___x_786_ = l_Lean_Elab_Command_elabCommand(v___x_785_, v___y_734_, v___y_735_);
                return v___x_786_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_803_);
                v___x_805_ = l_Array_append___redArg(v___y_803_, v___y_804_);
                crate::leanh::lean_dec_ref(v___y_804_);
                crate::leanh::lean_inc(v___y_801_);
                crate::leanh::lean_inc(v___y_793_);
                v___x_806_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_806_, 0, v___y_793_);
                crate::leanh::lean_ctor_set(v___x_806_, 1, v___y_801_);
                crate::leanh::lean_ctor_set(v___x_806_, 2, v___x_805_);
                if crate::leanh::lean_obj_tag(v___y_797_) == 1 {
                    v_val_807_ = crate::leanh::lean_ctor_get(v___y_797_, 0);
                    crate::leanh::lean_inc(v_val_807_);
                    crate::leanh::lean_dec_ref_known(v___y_797_, 1);
                    v___x_808_ = l_Array_mkArray1___redArg(v_val_807_);
                    v___y_730_ = v___y_790_;
                    v___y_731_ = v___y_791_;
                    v___y_732_ = v___y_792_;
                    v___y_733_ = v___y_793_;
                    v___y_734_ = v___y_794_;
                    v___y_735_ = v___y_795_;
                    v___y_736_ = v___y_796_;
                    v___y_737_ = v___x_806_;
                    v___y_738_ = v___y_798_;
                    v___y_739_ = v___y_799_;
                    v___y_740_ = v___y_800_;
                    v___y_741_ = v___y_801_;
                    v___y_742_ = v___y_802_;
                    v___y_743_ = v___y_803_;
                    v___y_744_ = v___x_808_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_797_);
                    v___x_809_ = l_Lean_Elab_Command_elabAuxDef___closed__9;
                    v___y_730_ = v___y_790_;
                    v___y_731_ = v___y_791_;
                    v___y_732_ = v___y_792_;
                    v___y_733_ = v___y_793_;
                    v___y_734_ = v___y_794_;
                    v___y_735_ = v___y_795_;
                    v___y_736_ = v___y_796_;
                    v___y_737_ = v___x_806_;
                    v___y_738_ = v___y_798_;
                    v___y_739_ = v___y_799_;
                    v___y_740_ = v___y_800_;
                    v___y_741_ = v___y_801_;
                    v___y_742_ = v___y_802_;
                    v___y_743_ = v___y_803_;
                    v___y_744_ = v___x_809_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_822_ = l_Lean_Elab_Command_elabAuxDef___closed__10;
                crate::leanh::lean_inc_ref_n(v___y_814_, 2);
                v___x_823_ = l_Lean_Name_mkStr4(v___x_725_, v___y_814_, v___x_726_, v___x_822_);
                v___x_824_ = l_Lean_Elab_Command_elabAuxDef___closed__11;
                v___x_825_ = l_Lean_Name_mkStr4(v___x_725_, v___y_814_, v___x_726_, v___x_824_);
                v___x_826_ = l_Lean_Elab_Command_elabAuxDef___closed__13;
                v___x_827_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabAuxDef___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabAuxDef___closed__14_once),
                    _init_l_Lean_Elab_Command_elabAuxDef___closed__14,
                );
                if crate::leanh::lean_obj_tag(v___y_812_) == 1 {
                    v_val_828_ = crate::leanh::lean_ctor_get(v___y_812_, 0);
                    crate::leanh::lean_inc(v_val_828_);
                    crate::leanh::lean_dec_ref_known(v___y_812_, 1);
                    v___x_829_ = l_Array_mkArray1___redArg(v_val_828_);
                    v___y_790_ = v___y_811_;
                    v___y_791_ = v___y_813_;
                    v___y_792_ = v___x_825_;
                    v___y_793_ = v___y_817_;
                    v___y_794_ = v___y_816_;
                    v___y_795_ = v___y_819_;
                    v___y_796_ = v___y_820_;
                    v___y_797_ = v___y_821_;
                    v___y_798_ = v___y_814_;
                    v___y_799_ = v___x_823_;
                    v___y_800_ = v___y_815_;
                    v___y_801_ = v___x_826_;
                    v___y_802_ = v___y_818_;
                    v___y_803_ = v___x_827_;
                    v___y_804_ = v___x_829_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_812_);
                    v___x_830_ = l_Lean_Elab_Command_elabAuxDef___closed__9;
                    v___y_790_ = v___y_811_;
                    v___y_791_ = v___y_813_;
                    v___y_792_ = v___x_825_;
                    v___y_793_ = v___y_817_;
                    v___y_794_ = v___y_816_;
                    v___y_795_ = v___y_819_;
                    v___y_796_ = v___y_820_;
                    v___y_797_ = v___y_821_;
                    v___y_798_ = v___y_814_;
                    v___y_799_ = v___x_823_;
                    v___y_800_ = v___y_815_;
                    v___y_801_ = v___x_826_;
                    v___y_802_ = v___y_818_;
                    v___y_803_ = v___x_827_;
                    v___y_804_ = v___x_830_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_843_ =
                    l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(
                        v___y_839_,
                    );
                v_a_844_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                crate::leanh::lean_inc(v_a_844_);
                crate::leanh::lean_dec_ref(v___x_843_);
                v___x_845_ = l_Lean_Elab_Command_getScope___redArg(v___y_839_);
                if crate::leanh::lean_obj_tag(v___x_845_) == 0 {
                    v_a_846_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                    crate::leanh::lean_inc(v_a_846_);
                    crate::leanh::lean_dec_ref_known(v___x_845_, 1);
                    v___x_847_ = lean_st_ref_get(v___y_839_);
                    v_currNamespace_848_ = crate::leanh::lean_ctor_get(v_a_846_, 2);
                    crate::leanh::lean_inc_n(v_currNamespace_848_, 2);
                    crate::leanh::lean_dec(v_a_846_);
                    v_env_849_ = crate::leanh::lean_ctor_get(v___x_847_, 0);
                    crate::leanh::lean_inc_ref(v_env_849_);
                    crate::leanh::lean_dec(v___x_847_);
                    v___x_850_ = l_Lean_Elab_Command_elabAuxDef___closed__16;
                    v___x_851_ = l_Lean_Name_append(v___x_850_, v_a_844_);
                    v___x_852_ = l_Lean_Elab_Command_elabAuxDef___closed__17;
                    v___x_853_ = l_Lean_Elab_Command_elabAuxDef___closed__18;
                    v___x_854_ = l_Lean_Name_append(v___x_851_, v___x_853_);
                    v___x_855_ = l_Lean_Name_append(v___x_854_, v___y_842_);
                    v___x_856_ = l_Lean_Name_components(v___x_855_);
                    v___x_857_ = crate::leanh::lean_box(0);
                    v___x_858_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabAuxDef_spec__2(
                        v___x_856_, v___x_857_,
                    );
                    v___x_859_ = l_String_intercalate(v___x_852_, v___x_858_);
                    v___x_860_ = l_Lean_Environment_setExporting(v_env_849_, v___x_728_);
                    v___x_861_ = l_Lean_DeclNameGenerator_ofPrefix(v_currNamespace_848_);
                    crate::leanh::lean_inc(v___y_833_);
                    v___x_862_ = l_Lean_Name_str___override(v___y_833_, v___x_859_);
                    v___x_863_ =
                        l_Lean_DeclNameGenerator_mkUniqueName(v___x_860_, v___x_861_, v___x_862_);
                    v_fst_864_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                    crate::leanh::lean_inc(v_fst_864_);
                    crate::leanh::lean_dec_ref(v___x_863_);
                    v___x_865_ = l_Lean_Elab_Command_getRef___redArg(v___y_837_);
                    if crate::leanh::lean_obj_tag(v___x_865_) == 0 {
                        v_a_866_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                        crate::leanh::lean_inc(v_a_866_);
                        crate::leanh::lean_dec_ref_known(v___x_865_, 1);
                        v___x_867_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_837_);
                        if crate::leanh::lean_obj_tag(v___x_867_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_867_, 1);
                            v_quotContext_x3f_868_ = crate::leanh::lean_ctor_get(v___y_837_, 5);
                            v___x_869_ = l_Lean_Name_replacePrefix(
                                v_fst_864_,
                                v_currNamespace_848_,
                                v___y_833_,
                            );
                            crate::leanh::lean_dec(v___y_833_);
                            crate::leanh::lean_dec(v_currNamespace_848_);
                            v___x_870_ = 0;
                            v___x_871_ = l_Lean_SourceInfo_fromRef(v_a_866_, v___x_870_);
                            crate::leanh::lean_dec(v_a_866_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_868_) == 0 {
                                v___x_872_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAuxDef_spec__1___redArg(v___y_839_);
                                crate::leanh::lean_dec_ref(v___x_872_);
                                v___y_811_ = v___y_832_;
                                v___y_812_ = v___y_834_;
                                v___y_813_ = v___x_869_;
                                v___y_814_ = v___y_835_;
                                v___y_815_ = v___y_836_;
                                v___y_816_ = v___y_837_;
                                v___y_817_ = v___x_871_;
                                v___y_818_ = v___y_838_;
                                v___y_819_ = v___y_839_;
                                v___y_820_ = v___y_840_;
                                v___y_821_ = v___y_841_;
                                state = 3;
                                continue;
                            } else {
                                v___y_811_ = v___y_832_;
                                v___y_812_ = v___y_834_;
                                v___y_813_ = v___x_869_;
                                v___y_814_ = v___y_835_;
                                v___y_815_ = v___y_836_;
                                v___y_816_ = v___y_837_;
                                v___y_817_ = v___x_871_;
                                v___y_818_ = v___y_838_;
                                v___y_819_ = v___y_839_;
                                v___y_820_ = v___y_840_;
                                v___y_821_ = v___y_841_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_866_);
                            crate::leanh::lean_dec(v_fst_864_);
                            crate::leanh::lean_dec(v_currNamespace_848_);
                            crate::leanh::lean_dec(v___y_841_);
                            crate::leanh::lean_dec(v___y_840_);
                            crate::leanh::lean_dec(v___y_838_);
                            crate::leanh::lean_dec(v___y_836_);
                            crate::leanh::lean_dec(v___y_834_);
                            crate::leanh::lean_dec(v___y_833_);
                            crate::leanh::lean_dec_ref(v___y_832_);
                            v_a_873_ = crate::leanh::lean_ctor_get(v___x_867_, 0);
                            v_isSharedCheck_880_ =
                                (!crate::leanh::lean_is_exclusive(v___x_867_)) as u8;
                            if v_isSharedCheck_880_ == 0 {
                                v___x_875_ = v___x_867_;
                                v_isShared_876_ = v_isSharedCheck_880_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_873_);
                                crate::leanh::lean_dec(v___x_867_);
                                v___x_875_ = crate::leanh::lean_box(0);
                                v_isShared_876_ = v_isSharedCheck_880_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_864_);
                        crate::leanh::lean_dec(v_currNamespace_848_);
                        crate::leanh::lean_dec(v___y_841_);
                        crate::leanh::lean_dec(v___y_840_);
                        crate::leanh::lean_dec(v___y_838_);
                        crate::leanh::lean_dec(v___y_836_);
                        crate::leanh::lean_dec(v___y_834_);
                        crate::leanh::lean_dec(v___y_833_);
                        crate::leanh::lean_dec_ref(v___y_832_);
                        v_a_881_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                        v_isSharedCheck_888_ = (!crate::leanh::lean_is_exclusive(v___x_865_)) as u8;
                        if v_isSharedCheck_888_ == 0 {
                            v___x_883_ = v___x_865_;
                            v_isShared_884_ = v_isSharedCheck_888_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_881_);
                            crate::leanh::lean_dec(v___x_865_);
                            v___x_883_ = crate::leanh::lean_box(0);
                            v_isShared_884_ = v_isSharedCheck_888_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_844_);
                    crate::leanh::lean_dec(v___y_842_);
                    crate::leanh::lean_dec(v___y_841_);
                    crate::leanh::lean_dec(v___y_840_);
                    crate::leanh::lean_dec(v___y_838_);
                    crate::leanh::lean_dec(v___y_836_);
                    crate::leanh::lean_dec(v___y_834_);
                    crate::leanh::lean_dec(v___y_833_);
                    crate::leanh::lean_dec_ref(v___y_832_);
                    v_a_889_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                    v_isSharedCheck_896_ = (!crate::leanh::lean_is_exclusive(v___x_845_)) as u8;
                    if v_isSharedCheck_896_ == 0 {
                        v___x_891_ = v___x_845_;
                        v_isShared_892_ = v_isSharedCheck_896_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_889_);
                        crate::leanh::lean_dec(v___x_845_);
                        v___x_891_ = crate::leanh::lean_box(0);
                        v_isShared_892_ = v_isSharedCheck_896_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_876_ == 0 {
                    v___x_878_ = v___x_875_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_878_;
            }
            7 => {
                if v_isShared_884_ == 0 {
                    v___x_886_ = v___x_883_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
                    v___x_886_ = v_reuseFailAlloc_887_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_886_;
            }
            9 => {
                if v_isShared_892_ == 0 {
                    v___x_894_ = v___x_891_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
                    v___x_894_ = v_reuseFailAlloc_895_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_894_;
            }
            11 => {
                v___x_902_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_903_ = l_Lean_Syntax_getArg(v_x_721_, v___x_902_);
                v___x_904_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_905_ = l_Lean_Syntax_getArg(v_x_721_, v___x_904_);
                v___x_906_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_907_ = l_Lean_Syntax_getArg(v_x_721_, v___x_906_);
                v___x_908_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_909_ = l_Lean_Syntax_getArg(v_x_721_, v___x_908_);
                crate::leanh::lean_dec(v_x_721_);
                v_suggestion_910_ = l_Lean_Syntax_getArgs(v___x_905_);
                crate::leanh::lean_dec(v___x_905_);
                v___x_911_ = l_Lean_Elab_Command_aux__def___closed__13;
                v___x_912_ = crate::leanh::lean_box(0);
                v_sz_913_ = lean_array_size(v_suggestion_910_);
                v___x_914_ = 0usize;
                crate::leanh::lean_inc_ref(v_suggestion_910_);
                v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabAuxDef_spec__3(v_sz_913_, v___x_914_, v_suggestion_910_);
                v___x_916_ = lean_array_get_size(v___x_915_);
                v___x_917_ = lean_nat_dec_lt(v___x_788_, v___x_916_);
                if v___x_917_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_915_);
                    v___y_832_ = v_suggestion_910_;
                    v___y_833_ = v___x_912_;
                    v___y_834_ = v___y_898_;
                    v___y_835_ = v___x_911_;
                    v___y_836_ = v___x_909_;
                    v___y_837_ = v___y_900_;
                    v___y_838_ = v___x_903_;
                    v___y_839_ = v___y_901_;
                    v___y_840_ = v___x_907_;
                    v___y_841_ = v_attrs_x3f_899_;
                    v___y_842_ = v___x_912_;
                    state = 4;
                    continue;
                } else {
                    v___x_918_ = lean_nat_dec_le(v___x_916_, v___x_916_);
                    if v___x_918_ == 0 {
                        if v___x_917_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_915_);
                            v___y_832_ = v_suggestion_910_;
                            v___y_833_ = v___x_912_;
                            v___y_834_ = v___y_898_;
                            v___y_835_ = v___x_911_;
                            v___y_836_ = v___x_909_;
                            v___y_837_ = v___y_900_;
                            v___y_838_ = v___x_903_;
                            v___y_839_ = v___y_901_;
                            v___y_840_ = v___x_907_;
                            v___y_841_ = v_attrs_x3f_899_;
                            v___y_842_ = v___x_912_;
                            state = 4;
                            continue;
                        } else {
                            v___x_919_ = lean_usize_of_nat(v___x_916_);
                            v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_915_, v___x_914_, v___x_919_, v___x_912_);
                            crate::leanh::lean_dec_ref(v___x_915_);
                            v___y_832_ = v_suggestion_910_;
                            v___y_833_ = v___x_912_;
                            v___y_834_ = v___y_898_;
                            v___y_835_ = v___x_911_;
                            v___y_836_ = v___x_909_;
                            v___y_837_ = v___y_900_;
                            v___y_838_ = v___x_903_;
                            v___y_839_ = v___y_901_;
                            v___y_840_ = v___x_907_;
                            v___y_841_ = v_attrs_x3f_899_;
                            v___y_842_ = v___x_920_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_921_ = lean_usize_of_nat(v___x_916_);
                        v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabAuxDef_spec__4(v___x_915_, v___x_914_, v___x_921_, v___x_912_);
                        crate::leanh::lean_dec_ref(v___x_915_);
                        v___y_832_ = v_suggestion_910_;
                        v___y_833_ = v___x_912_;
                        v___y_834_ = v___y_898_;
                        v___y_835_ = v___x_911_;
                        v___y_836_ = v___x_909_;
                        v___y_837_ = v___y_900_;
                        v___y_838_ = v___x_903_;
                        v___y_839_ = v___y_901_;
                        v___y_840_ = v___x_907_;
                        v___y_841_ = v_attrs_x3f_899_;
                        v___y_842_ = v___x_922_;
                        state = 4;
                        continue;
                    }
                }
            }
            12 => {
                v___x_927_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_928_ = l_Lean_Syntax_getArg(v_x_721_, v___x_927_);
                v___x_929_ = l_Lean_Syntax_isNone(v___x_928_);
                if v___x_929_ == 0 {
                    crate::leanh::lean_inc(v___x_928_);
                    v___x_930_ = l_Lean_Syntax_matchesNull(v___x_928_, v___x_927_);
                    if v___x_930_ == 0 {
                        crate::leanh::lean_dec(v___x_928_);
                        crate::leanh::lean_dec(v_doc_x3f_924_);
                        crate::leanh::lean_dec(v_x_721_);
                        v___x_931_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
                        return v___x_931_;
                    } else {
                        v_attrs_x3f_932_ = l_Lean_Syntax_getArg(v___x_928_, v___x_788_);
                        crate::leanh::lean_dec(v___x_928_);
                        v___x_933_ = l_Lean_Elab_Command_aux__def___closed__16;
                        crate::leanh::lean_inc(v_attrs_x3f_932_);
                        v___x_934_ = l_Lean_Syntax_isOfKind(v_attrs_x3f_932_, v___x_933_);
                        if v___x_934_ == 0 {
                            crate::leanh::lean_dec(v_attrs_x3f_932_);
                            crate::leanh::lean_dec(v_doc_x3f_924_);
                            crate::leanh::lean_dec(v_x_721_);
                            v___x_935_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabAuxDef_spec__0___redArg();
                            return v___x_935_;
                        } else {
                            v___x_936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_936_, 0, v_attrs_x3f_932_);
                            v___y_898_ = v_doc_x3f_924_;
                            v_attrs_x3f_899_ = v___x_936_;
                            v___y_900_ = v___y_925_;
                            v___y_901_ = v___y_926_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_928_);
                    v___x_937_ = crate::leanh::lean_box(0);
                    v___y_898_ = v_doc_x3f_924_;
                    v_attrs_x3f_899_ = v___x_937_;
                    v___y_900_ = v___y_925_;
                    v___y_901_ = v___y_926_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabAuxDef___boxed(
    mut v_x_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Lean_Elab_Command_elabAuxDef(v_x_949_, v_a_950_, v_a_951_);
    crate::leanh::lean_dec(v_a_951_);
    crate::leanh::lean_dec_ref(v_a_950_);
    return v_res_953_;
}
pub unsafe fn l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_962_ = l_Lean_Elab_Command_aux__def___closed__4;
    v___x_963_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1;
    v___x_964_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabAuxDef___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_965_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_961_, v___x_962_, v___x_963_, v___x_964_,
    );
    return v___x_965_;
}
pub unsafe fn l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___boxed(
    mut v_a_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
    return v_res_967_;
}
pub unsafe fn l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1___closed__1;
    v___x_995_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___closed__6;
    v___x_996_ = l_Lean_addBuiltinDeclarationRanges(v___x_994_, v___x_995_);
    return v___x_996_;
}
pub unsafe fn l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3___boxed(
    mut v_a_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_998_ = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
    return v_res_998_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_AuxDef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AuxDef_0__Lean_Elab_Command_elabAuxDef___regBuiltin_Lean_Elab_Command_elabAuxDef_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_AuxDef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_AuxDef(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_AuxDef(builtin);
}

// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.RegisterCommand
// Imports: Lean.Meta.Tactic.Simp.Attr Lean.Meta.Tactic.Simp.Simproc
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Extra::l_String_removeLeadingSpaces;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getDocString, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr8,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::{
    initialize_Lean_Meta_Tactic_Simp_Attr, runtime_initialize_Lean_Meta_Tactic_Simp_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName,
    meta_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Parser_Command_registerSimpAttr___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [83, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__3_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [95, 114, 111, 111, 116, 95, 0],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__4_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__6_value: LeanStringObject<17> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 83, 105, 109, 112, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__6_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__2_value)
                as *mut LeanObject,
            492087047182689846 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_3: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__3_value)
                as *mut LeanObject,
            3807465732421683321 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_4: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value)
                as *mut LeanObject,
            11003384106879496924 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_5: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_4)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value)
                as *mut LeanObject,
            6424342348527123813 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_6: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_5)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value)
                as *mut LeanObject,
            398612535786245292 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_registerSimpAttr___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value_aux_6)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__6_value)
                as *mut LeanObject,
            6403652195904713004 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__8_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__8_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__10_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__10_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__12_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__12_value)
                as *mut LeanObject,
            3961966953292576997 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__16_value: LeanStringObject<19> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 95, 115, 105, 109, 112, 95, 97, 116, 116, 114,
            0,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__19_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Command_registerSimpAttr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__19_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerSimpAttr___closed__23_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__7_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerSimpAttr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__23_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_registerSimpAttr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value) as *mut LeanObject,17416048715816169289 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__3_value) as *mut LeanObject,18184376426117065311 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0_value) as *mut LeanObject,9480010471355609749 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5_value) as *mut LeanObject,2812521669163367463 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__8_value) as *mut LeanObject,17682753938374962505 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 111, 109, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__15_value) as *mut LeanObject,6376237424612349584 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 120, 95, 63, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__17_value) as *mut LeanObject,14916367973757185555 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__19_value) as *mut LeanObject,14182491107802134955 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 120, 95, 60, 124, 62, 95, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__21_value) as *mut LeanObject,7409751955955409350 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 97, 116, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__23_value) as *mut LeanObject,14125453249386077023 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [80, 97, 114, 115, 101, 114, 46, 84, 97, 99, 116, 105, 99, 46, 115, 105, 109, 112, 80, 114, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 80, 114, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,6907480769838958894 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value) as *mut LeanObject,357025339588547027 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value) as *mut LeanObject,16665139701948437588 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__28_value) as *mut LeanObject,10994783280459430853 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 124, 62, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [80, 97, 114, 115, 101, 114, 46, 84, 97, 99, 116, 105, 99, 46, 115, 105, 109, 112, 80, 111, 115, 116, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 80, 111, 115, 116, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,6907480769838958894 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value) as *mut LeanObject,357025339588547027 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value) as *mut LeanObject,9114251629459821975 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__27_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__34_value) as *mut LeanObject,11666232682930756134 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 105, 99, 111, 100, 101, 65, 116, 111, 109, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__14_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__38_value) as *mut LeanObject,7882745399186723613 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 110, 105, 99, 111, 100, 101, 40, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__41_value) as *mut LeanObject,9232979286016572671 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 4, m_data: [34, 226, 134, 144, 32, 34, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [34, 60, 45, 32, 34, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 105, 111, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46_value) as *mut LeanObject,17836958171642591098 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49_value) as *mut LeanObject,6289677862665402693 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__12_value) as *mut LeanObject,9063780239635860524 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [47, 45, 45, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [83, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 32, 45, 47, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 120, 116, 80, 114, 111, 99, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55_value) as *mut LeanObject,8667906478939170201 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 105, 109, 112, 114, 111, 99, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value) as *mut LeanObject,3280738234411178544 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__2_value) as *mut LeanObject,492087047182689846 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58_value) as *mut LeanObject,17322321828708229441 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61_value) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 83, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value) as *mut LeanObject,3718849471849338521 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__2_value) as *mut LeanObject,492087047182689846 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63_value) as *mut LeanObject,10319981540172179672 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70_value) as *mut LeanObject,10411423847645546083 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72_value) as *mut LeanObject,4787239732180154236 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__74_value) as *mut LeanObject,387456110215466097 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76_value) as *mut LeanObject,6455343056875556081 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__80_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value) as *mut LeanObject,1830315843745225569 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83_value) as *mut LeanObject,12042283042177957812 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__86_value) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__88_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__87_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__89_value) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__92_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__94_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__96_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__98_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__6_value) as *mut LeanObject,8338287878077902919 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__6_value) as *mut LeanObject,10793207103888482170 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__102_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__103_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 114, 111, 99, 32, 115, 101, 116, 32, 102, 111, 114, 32, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__107_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109_value) as *mut LeanObject,12014440461648055863 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__111_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value) as *mut LeanObject;
static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSimpAttr___closed__4_value) as *mut LeanObject,6907480769838958894 as *mut LeanObject] };
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__115_value) as *mut LeanObject,16282038225239345418 as *mut LeanObject] };
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 105, 109, 112, 32, 115, 101, 116, 32, 102, 111, 114, 32, 0]};
static mut l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1()
-> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_751_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__0;
    v___x_752_ = l_String_toRawSubstring_x27(v___x_751_);
    return v___x_752_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26()
-> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__25;
    v___x_803_ = l_String_toRawSubstring_x27(v___x_802_);
    return v___x_803_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33()
-> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__32;
    v___x_818_ = l_String_toRawSubstring_x27(v___x_817_);
    return v___x_818_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47()
-> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__46;
    v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
    return v___x_845_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50()
-> *mut LeanObject {
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__49;
    v___x_850_ = l_String_toRawSubstring_x27(v___x_849_);
    return v___x_850_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56()
-> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__55;
    v___x_862_ = l_String_toRawSubstring_x27(v___x_861_);
    return v___x_862_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59()
-> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__58;
    v___x_867_ = l_String_toRawSubstring_x27(v___x_866_);
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64()
-> *mut LeanObject {
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__63;
    v___x_879_ = l_String_toRawSubstring_x27(v___x_878_);
    return v___x_879_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77()
-> *mut LeanObject {
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__76;
    v___x_910_ = l_String_toRawSubstring_x27(v___x_909_);
    return v___x_910_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84()
-> *mut LeanObject {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_922_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__83;
    v___x_923_ = l_String_toRawSubstring_x27(v___x_922_);
    return v___x_923_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100()
-> *mut LeanObject {
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_966_ = l_Lean_Parser_Command_registerSimpAttr___closed__6;
    v___x_967_ = l_String_toRawSubstring_x27(v___x_966_);
    return v___x_967_;
}
pub unsafe fn _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113()
-> *mut LeanObject {
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_1001_ = l_Array_mkArray0(lean_box(0));
    return v___x_1001_;
}
pub unsafe fn l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(
    mut v_x_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1344_: u8 = 0;
    let mut v___y_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_procId_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_procStr_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_procIdParser_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v_idParser_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1082_ = l_Lean_Parser_Command_registerSimpAttr___closed__0;
                v___x_1083_ = l_Lean_Parser_Command_registerSimpAttr___closed__4;
                v___x_1333_ = l_Lean_Parser_Command_registerSimpAttr___closed__7;
                lean_inc(v_x_1009_);
                v___x_1334_ = l_Lean_Syntax_isOfKind(v_x_1009_, v___x_1333_);
                if v___x_1334_ == 0 {
                    lean_dec(v_x_1009_);
                    v___x_1335_ = lean_box(1);
                    v___x_1336_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1336_, 0, v___x_1335_);
                    lean_ctor_set(v___x_1336_, 1, v_a_1011_);
                    return v___x_1336_;
                } else {
                    v___x_1337_ = lean_unsigned_to_nat(0);
                    v___x_1338_ = l_Lean_Syntax_getArg(v_x_1009_, v___x_1337_);
                    v___x_1339_ = lean_unsigned_to_nat(2);
                    v_id_1340_ = l_Lean_Syntax_getArg(v_x_1009_, v___x_1339_);
                    lean_dec(v_x_1009_);
                    v___x_1385_ = l_Lean_Syntax_getOptional_x3f(v___x_1338_);
                    lean_dec(v___x_1338_);
                    if lean_obj_tag(v___x_1385_) == 0 {
                        v___x_1386_ = lean_box(0);
                        v___y_1374_ = v___x_1386_;
                        state = 5;
                        continue;
                    } else {
                        v_val_1387_ = lean_ctor_get(v___x_1385_, 0);
                        v_isSharedCheck_1394_ = (!lean_is_exclusive(v___x_1385_)) as u8;
                        if v_isSharedCheck_1394_ == 0 {
                            v___x_1389_ = v___x_1385_;
                            v_isShared_1390_ = v_isSharedCheck_1394_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_val_1387_);
                            lean_dec(v___x_1385_);
                            v___x_1389_ = lean_box(0);
                            v_isShared_1390_ = v_isSharedCheck_1394_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1050_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__1);
                v___x_1051_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__2;
                lean_inc(v___y_1017_);
                lean_inc(v___y_1035_);
                v___x_1052_ = l_Lean_addMacroScope(v___y_1035_, v___x_1051_, v___y_1017_);
                v___x_1053_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__4;
                v___x_1054_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1054_, 0, v___x_1053_);
                lean_ctor_set(v___x_1054_, 1, v___y_1016_);
                v___x_1055_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1055_, 0, v___x_1054_);
                lean_ctor_set(v___x_1055_, 1, v___y_1020_);
                lean_inc_n(v___y_1026_, 13);
                v___x_1056_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1056_, 0, v___y_1026_);
                lean_ctor_set(v___x_1056_, 1, v___x_1050_);
                lean_ctor_set(v___x_1056_, 2, v___x_1052_);
                lean_ctor_set(v___x_1056_, 3, v___x_1055_);
                lean_inc_n(v___y_1046_, 5);
                v___x_1057_ = l_Lean_Syntax_node3(
                    v___y_1026_,
                    v___y_1046_,
                    v___y_1049_,
                    v___y_1044_,
                    v___x_1056_,
                );
                lean_inc(v___y_1032_);
                v___x_1058_ =
                    l_Lean_Syntax_node2(v___y_1026_, v___y_1032_, v___y_1027_, v___x_1057_);
                lean_inc(v___y_1045_);
                v___x_1059_ = l_Lean_Syntax_node1(v___y_1026_, v___y_1045_, v___x_1058_);
                lean_inc_n(v___y_1031_, 3);
                lean_inc(v___y_1040_);
                v___x_1060_ =
                    l_Lean_Syntax_node2(v___y_1026_, v___y_1040_, v___x_1059_, v___y_1031_);
                v___x_1061_ = l_Lean_Syntax_node1(v___y_1026_, v___y_1046_, v___x_1060_);
                lean_inc(v___y_1024_);
                v___x_1062_ = l_Lean_Syntax_node1(v___y_1026_, v___y_1024_, v___x_1061_);
                lean_inc(v___y_1041_);
                v___x_1063_ = l_Lean_Syntax_node4(
                    v___y_1026_,
                    v___y_1041_,
                    v___y_1033_,
                    v___y_1022_,
                    v___y_1037_,
                    v___x_1062_,
                );
                v___x_1064_ = l_Lean_Syntax_node5(
                    v___y_1026_,
                    v___y_1043_,
                    v___y_1034_,
                    v___y_1036_,
                    v___y_1023_,
                    v___y_1028_,
                    v___y_1025_,
                );
                v___x_1065_ = l_Lean_Syntax_node1(v___y_1026_, v___y_1046_, v___x_1064_);
                v___x_1066_ = l_Lean_Syntax_mkStrLit(v___y_1047_, v___y_1018_);
                v___x_1067_ = l_Lean_Syntax_node1(v___y_1026_, v___y_1048_, v___x_1066_);
                v___x_1068_ =
                    l_Lean_Syntax_node2(v___y_1026_, v___y_1046_, v___x_1067_, v___y_1030_);
                v___x_1069_ = lean_array_push(v___y_1013_, v___y_1029_);
                v___x_1070_ = lean_array_push(v___x_1069_, v___y_1031_);
                v___x_1071_ = lean_array_push(v___x_1070_, v___y_1014_);
                v___x_1072_ = lean_array_push(v___x_1071_, v___y_1038_);
                v___x_1073_ = lean_array_push(v___x_1072_, v___y_1031_);
                v___x_1074_ = lean_array_push(v___x_1073_, v___x_1065_);
                v___x_1075_ = lean_array_push(v___x_1074_, v___y_1031_);
                v___x_1076_ = lean_array_push(v___x_1075_, v___x_1068_);
                v___x_1077_ = lean_array_push(v___x_1076_, v___y_1042_);
                v___x_1078_ = lean_array_push(v___x_1077_, v___y_1019_);
                lean_inc(v___y_1015_);
                v___x_1079_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1079_, 0, v___y_1026_);
                lean_ctor_set(v___x_1079_, 1, v___y_1015_);
                lean_ctor_set(v___x_1079_, 2, v___x_1078_);
                v___x_1080_ = l_Lean_Syntax_node4(
                    v___y_1026_,
                    v___y_1046_,
                    v___y_1039_,
                    v___y_1021_,
                    v___x_1063_,
                    v___x_1079_,
                );
                v___x_1081_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1081_, 0, v___x_1080_);
                lean_ctor_set(v___x_1081_, 1, v_a_1011_);
                return v___x_1081_;
            }
            2 => {
                lean_inc_n(v___y_1115_, 8);
                lean_inc_n(v___y_1095_, 52);
                v___x_1118_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___y_1115_, v___y_1117_, v___y_1100_);
                lean_inc(v___y_1101_);
                v___x_1119_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___y_1101_, v___y_1109_, v___x_1118_);
                lean_inc(v___y_1114_);
                v___x_1120_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1114_, v___x_1119_);
                lean_inc_n(v___y_1098_, 13);
                lean_inc(v___y_1106_);
                v___x_1121_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___y_1106_, v___x_1120_, v___y_1098_);
                v___x_1122_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1115_, v___x_1121_);
                lean_inc(v___y_1093_);
                v___x_1123_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1093_, v___x_1122_);
                lean_inc(v___y_1092_);
                lean_inc(v___y_1108_);
                v___x_1124_ = l_Lean_Syntax_node4(
                    v___y_1095_,
                    v___y_1108_,
                    v___y_1105_,
                    v___y_1092_,
                    v___y_1107_,
                    v___x_1123_,
                );
                v___x_1125_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__5;
                v___x_1126_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__6;
                v___x_1127_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__7;
                lean_inc_ref(v___y_1113_);
                v___x_1128_ =
                    l_Lean_Name_mkStr4(v___x_1082_, v___x_1083_, v___y_1113_, v___x_1127_);
                v___x_1129_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1128_, v___y_1098_);
                v___x_1130_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1130_, 0, v___y_1095_);
                lean_ctor_set(v___x_1130_, 1, v___x_1125_);
                v___x_1131_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__9;
                v___x_1132_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__10;
                v___x_1133_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1133_, 0, v___y_1095_);
                lean_ctor_set(v___x_1133_, 1, v___x_1132_);
                v___x_1134_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__11;
                v___x_1135_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1135_, 0, v___y_1095_);
                lean_ctor_set(v___x_1135_, 1, v___x_1134_);
                v___x_1136_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__12;
                v___x_1137_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1137_, 0, v___y_1095_);
                lean_ctor_set(v___x_1137_, 1, v___x_1136_);
                v___x_1138_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__13;
                v___x_1139_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1139_, 0, v___y_1095_);
                lean_ctor_set(v___x_1139_, 1, v___x_1138_);
                lean_inc_ref_n(v___x_1139_, 4);
                lean_inc_ref(v___x_1137_);
                lean_inc_ref(v___x_1135_);
                lean_inc_ref_n(v___x_1133_, 3);
                v___x_1140_ = l_Lean_Syntax_node5(
                    v___y_1095_,
                    v___x_1131_,
                    v___x_1133_,
                    v___x_1135_,
                    v___x_1137_,
                    v___y_1110_,
                    v___x_1139_,
                );
                v___x_1141_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1115_, v___x_1140_);
                v___x_1142_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__16;
                lean_inc(v___y_1089_);
                v___x_1143_ = l_Lean_Syntax_mkStrLit(v___y_1097_, v___y_1089_);
                v___x_1144_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1142_, v___x_1143_);
                v___x_1145_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__18;
                v___x_1146_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__20;
                v___x_1147_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__22;
                v___x_1148_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__24;
                v___x_1149_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__26);
                v___x_1150_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__29;
                lean_inc_n(v___y_1087_, 7);
                lean_inc_n(v___y_1102_, 7);
                v___x_1151_ = l_Lean_addMacroScope(v___y_1102_, v___x_1150_, v___y_1087_);
                v___x_1152_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__30;
                lean_inc_n(v___y_1088_, 5);
                v___x_1153_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1153_, 0, v___x_1152_);
                lean_ctor_set(v___x_1153_, 1, v___y_1088_);
                lean_inc_n(v___y_1090_, 7);
                v___x_1154_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1154_, 0, v___x_1153_);
                lean_ctor_set(v___x_1154_, 1, v___y_1090_);
                v___x_1155_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1155_, 0, v___y_1095_);
                lean_ctor_set(v___x_1155_, 1, v___x_1149_);
                lean_ctor_set(v___x_1155_, 2, v___x_1151_);
                lean_ctor_set(v___x_1155_, 3, v___x_1154_);
                v___x_1156_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1148_, v___x_1155_, v___y_1098_);
                v___x_1157_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__31;
                v___x_1158_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1158_, 0, v___y_1095_);
                lean_ctor_set(v___x_1158_, 1, v___x_1157_);
                v___x_1159_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__33);
                v___x_1160_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__35;
                v___x_1161_ = l_Lean_addMacroScope(v___y_1102_, v___x_1160_, v___y_1087_);
                v___x_1162_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__36;
                v___x_1163_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1163_, 0, v___x_1162_);
                lean_ctor_set(v___x_1163_, 1, v___y_1088_);
                v___x_1164_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1164_, 0, v___x_1163_);
                lean_ctor_set(v___x_1164_, 1, v___y_1090_);
                v___x_1165_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1165_, 0, v___y_1095_);
                lean_ctor_set(v___x_1165_, 1, v___x_1159_);
                lean_ctor_set(v___x_1165_, 2, v___x_1161_);
                lean_ctor_set(v___x_1165_, 3, v___x_1164_);
                v___x_1166_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1148_, v___x_1165_, v___y_1098_);
                v___x_1167_ = l_Lean_Syntax_node3(
                    v___y_1095_,
                    v___x_1147_,
                    v___x_1156_,
                    v___x_1158_,
                    v___x_1166_,
                );
                v___x_1168_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1115_, v___x_1167_);
                v___x_1169_ = l_Lean_Syntax_node3(
                    v___y_1095_,
                    v___x_1146_,
                    v___x_1133_,
                    v___x_1168_,
                    v___x_1139_,
                );
                v___x_1170_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__37;
                v___x_1171_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1171_, 0, v___y_1095_);
                lean_ctor_set(v___x_1171_, 1, v___x_1170_);
                lean_inc_ref_n(v___x_1171_, 2);
                v___x_1172_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1145_, v___x_1169_, v___x_1171_);
                v___x_1173_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__39;
                v___x_1174_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__40;
                v___x_1175_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1175_, 0, v___y_1095_);
                lean_ctor_set(v___x_1175_, 1, v___x_1174_);
                v___x_1176_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__42;
                v___x_1177_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__43;
                v___x_1178_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1178_, 0, v___y_1095_);
                lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                v___x_1179_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1176_, v___x_1178_);
                v___x_1180_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__44;
                v___x_1181_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1181_, 0, v___y_1095_);
                lean_ctor_set(v___x_1181_, 1, v___x_1180_);
                v___x_1182_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__45;
                v___x_1183_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1183_, 0, v___y_1095_);
                lean_ctor_set(v___x_1183_, 1, v___x_1182_);
                v___x_1184_ = l_Lean_Syntax_node1(v___y_1095_, v___x_1176_, v___x_1183_);
                v___x_1185_ = l_Lean_Syntax_node6(
                    v___y_1095_,
                    v___x_1173_,
                    v___x_1175_,
                    v___x_1179_,
                    v___x_1181_,
                    v___x_1184_,
                    v___y_1098_,
                    v___x_1139_,
                );
                v___x_1186_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1145_, v___x_1185_, v___x_1171_);
                v___x_1187_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__47);
                v___x_1188_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__48;
                v___x_1189_ = l_Lean_addMacroScope(v___y_1102_, v___x_1188_, v___y_1087_);
                v___x_1190_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1190_, 0, v___y_1095_);
                lean_ctor_set(v___x_1190_, 1, v___x_1187_);
                lean_ctor_set(v___x_1190_, 2, v___x_1189_);
                lean_ctor_set(v___x_1190_, 3, v___y_1090_);
                v___x_1191_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1148_, v___x_1190_, v___y_1098_);
                v___x_1192_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1115_, v___x_1191_);
                v___x_1193_ = l_Lean_Syntax_node3(
                    v___y_1095_,
                    v___x_1146_,
                    v___x_1133_,
                    v___x_1192_,
                    v___x_1139_,
                );
                v___x_1194_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1145_, v___x_1193_, v___x_1171_);
                lean_inc(v___x_1172_);
                v___x_1195_ = l_Lean_Syntax_node4(
                    v___y_1095_,
                    v___y_1115_,
                    v___x_1144_,
                    v___x_1172_,
                    v___x_1186_,
                    v___x_1194_,
                );
                v___x_1196_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__50);
                v___x_1197_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__51;
                v___x_1198_ = l_Lean_addMacroScope(v___y_1102_, v___x_1197_, v___y_1087_);
                v___x_1199_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1199_, 0, v___y_1095_);
                lean_ctor_set(v___x_1199_, 1, v___x_1196_);
                lean_ctor_set(v___x_1199_, 2, v___x_1198_);
                lean_ctor_set(v___x_1199_, 3, v___y_1090_);
                v___x_1200_ = lean_unsigned_to_nat(10);
                v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
                lean_inc_ref(v___x_1201_);
                v___x_1202_ = lean_array_push(v___x_1201_, v___y_1086_);
                v___x_1203_ = lean_array_push(v___x_1202_, v___y_1098_);
                lean_inc(v___x_1129_);
                v___x_1204_ = lean_array_push(v___x_1203_, v___x_1129_);
                lean_inc_ref(v___x_1130_);
                v___x_1205_ = lean_array_push(v___x_1204_, v___x_1130_);
                v___x_1206_ = lean_array_push(v___x_1205_, v___y_1098_);
                v___x_1207_ = lean_array_push(v___x_1206_, v___x_1141_);
                v___x_1208_ = lean_array_push(v___x_1207_, v___y_1098_);
                v___x_1209_ = lean_array_push(v___x_1208_, v___x_1195_);
                lean_inc_n(v___y_1111_, 2);
                v___x_1210_ = lean_array_push(v___x_1209_, v___y_1111_);
                lean_inc_ref(v___x_1199_);
                v___x_1211_ = lean_array_push(v___x_1210_, v___x_1199_);
                v___x_1212_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1212_, 0, v___y_1095_);
                lean_ctor_set(v___x_1212_, 1, v___x_1126_);
                lean_ctor_set(v___x_1212_, 2, v___x_1211_);
                v___x_1213_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__52;
                v___x_1214_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__53;
                v___x_1215_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1215_, 0, v___y_1095_);
                lean_ctor_set(v___x_1215_, 1, v___x_1214_);
                v___x_1216_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__54;
                v___x_1217_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1217_, 0, v___y_1095_);
                lean_ctor_set(v___x_1217_, 1, v___x_1216_);
                v___x_1218_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___x_1213_, v___x_1215_, v___x_1217_);
                v___x_1219_ = l_Lean_Syntax_node1(v___y_1095_, v___y_1115_, v___x_1218_);
                lean_inc(v___x_1219_);
                lean_inc(v___y_1103_);
                v___x_1220_ = l_Lean_Syntax_node7(
                    v___y_1095_,
                    v___y_1103_,
                    v___x_1219_,
                    v___y_1098_,
                    v___y_1104_,
                    v___y_1098_,
                    v___y_1099_,
                    v___y_1098_,
                    v___y_1098_,
                );
                v___x_1221_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__56);
                v___x_1222_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__57;
                v___x_1223_ = l_Lean_addMacroScope(v___y_1102_, v___x_1222_, v___y_1087_);
                v___x_1224_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1224_, 0, v___y_1095_);
                lean_ctor_set(v___x_1224_, 1, v___x_1221_);
                lean_ctor_set(v___x_1224_, 2, v___x_1223_);
                lean_ctor_set(v___x_1224_, 3, v___y_1090_);
                v___x_1225_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__59);
                v___x_1226_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__60;
                v___x_1227_ = l_Lean_addMacroScope(v___y_1102_, v___x_1226_, v___y_1087_);
                v___x_1228_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__61;
                v___x_1229_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1229_, 0, v___x_1228_);
                lean_ctor_set(v___x_1229_, 1, v___y_1088_);
                v___x_1230_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__62;
                v___x_1231_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1231_, 0, v___x_1230_);
                lean_ctor_set(v___x_1231_, 1, v___y_1090_);
                v___x_1232_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1232_, 0, v___x_1229_);
                lean_ctor_set(v___x_1232_, 1, v___x_1231_);
                v___x_1233_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1233_, 0, v___y_1095_);
                lean_ctor_set(v___x_1233_, 1, v___x_1225_);
                lean_ctor_set(v___x_1233_, 2, v___x_1227_);
                lean_ctor_set(v___x_1233_, 3, v___x_1232_);
                v___x_1234_ =
                    l_Lean_Syntax_node2(v___y_1095_, v___y_1085_, v___y_1111_, v___x_1233_);
                v___x_1235_ = l_Lean_Syntax_node3(
                    v___y_1095_,
                    v___y_1115_,
                    v___x_1224_,
                    v___x_1234_,
                    v___y_1094_,
                );
                v___x_1236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__64);
                v___x_1237_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__65;
                v___x_1238_ = l_Lean_addMacroScope(v___y_1102_, v___x_1237_, v___y_1087_);
                v___x_1239_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__66;
                v___x_1240_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1240_, 0, v___x_1239_);
                lean_ctor_set(v___x_1240_, 1, v___y_1088_);
                v___x_1241_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1241_, 0, v___x_1240_);
                lean_ctor_set(v___x_1241_, 1, v___y_1090_);
                v___x_1242_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1242_, 0, v___y_1095_);
                lean_ctor_set(v___x_1242_, 1, v___x_1236_);
                lean_ctor_set(v___x_1242_, 2, v___x_1238_);
                lean_ctor_set(v___x_1242_, 3, v___x_1241_);
                lean_inc(v___y_1091_);
                v___x_1243_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___y_1088_,
                    v___y_1091_,
                );
                if lean_obj_tag(v___x_1243_) == 0 {
                    v___x_1244_ = l_Lean_quoteNameMk(v___y_1091_);
                    v___y_1013_ = v___x_1201_;
                    v___y_1014_ = v___x_1129_;
                    v___y_1015_ = v___x_1126_;
                    v___y_1016_ = v___y_1088_;
                    v___y_1017_ = v___y_1087_;
                    v___y_1018_ = v___y_1089_;
                    v___y_1019_ = v___x_1199_;
                    v___y_1020_ = v___y_1090_;
                    v___y_1021_ = v___x_1212_;
                    v___y_1022_ = v___y_1092_;
                    v___y_1023_ = v___x_1137_;
                    v___y_1024_ = v___y_1093_;
                    v___y_1025_ = v___x_1139_;
                    v___y_1026_ = v___y_1095_;
                    v___y_1027_ = v___x_1242_;
                    v___y_1028_ = v___y_1096_;
                    v___y_1029_ = v___x_1219_;
                    v___y_1030_ = v___x_1172_;
                    v___y_1031_ = v___y_1098_;
                    v___y_1032_ = v___y_1101_;
                    v___y_1033_ = v___x_1220_;
                    v___y_1034_ = v___x_1133_;
                    v___y_1035_ = v___y_1102_;
                    v___y_1036_ = v___x_1135_;
                    v___y_1037_ = v___x_1235_;
                    v___y_1038_ = v___x_1130_;
                    v___y_1039_ = v___x_1124_;
                    v___y_1040_ = v___y_1106_;
                    v___y_1041_ = v___y_1108_;
                    v___y_1042_ = v___y_1111_;
                    v___y_1043_ = v___x_1131_;
                    v___y_1044_ = v___y_1112_;
                    v___y_1045_ = v___y_1114_;
                    v___y_1046_ = v___y_1115_;
                    v___y_1047_ = v___y_1116_;
                    v___y_1048_ = v___x_1142_;
                    v___y_1049_ = v___x_1244_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1091_);
                    v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
                    lean_inc(v_val_1245_);
                    lean_dec_ref_known(v___x_1243_, 1);
                    v___x_1246_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__67;
                    lean_inc_ref(v___y_1113_);
                    v___x_1247_ =
                        l_Lean_Name_mkStr4(v___x_1082_, v___x_1083_, v___y_1113_, v___x_1246_);
                    v___x_1248_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68;
                    v___x_1249_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69;
                    v___x_1250_ = lean_string_intercalate(v___x_1249_, v_val_1245_);
                    v___x_1251_ = lean_string_append(v___x_1248_, v___x_1250_);
                    lean_dec_ref(v___x_1250_);
                    lean_inc_n(v___y_1089_, 2);
                    v___x_1252_ = l_Lean_Syntax_mkNameLit(v___x_1251_, v___y_1089_);
                    v___x_1253_ = lean_unsigned_to_nat(1);
                    v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
                    v___x_1255_ = lean_array_push(v___x_1254_, v___x_1252_);
                    v___x_1256_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1256_, 0, v___y_1089_);
                    lean_ctor_set(v___x_1256_, 1, v___x_1247_);
                    lean_ctor_set(v___x_1256_, 2, v___x_1255_);
                    v___y_1013_ = v___x_1201_;
                    v___y_1014_ = v___x_1129_;
                    v___y_1015_ = v___x_1126_;
                    v___y_1016_ = v___y_1088_;
                    v___y_1017_ = v___y_1087_;
                    v___y_1018_ = v___y_1089_;
                    v___y_1019_ = v___x_1199_;
                    v___y_1020_ = v___y_1090_;
                    v___y_1021_ = v___x_1212_;
                    v___y_1022_ = v___y_1092_;
                    v___y_1023_ = v___x_1137_;
                    v___y_1024_ = v___y_1093_;
                    v___y_1025_ = v___x_1139_;
                    v___y_1026_ = v___y_1095_;
                    v___y_1027_ = v___x_1242_;
                    v___y_1028_ = v___y_1096_;
                    v___y_1029_ = v___x_1219_;
                    v___y_1030_ = v___x_1172_;
                    v___y_1031_ = v___y_1098_;
                    v___y_1032_ = v___y_1101_;
                    v___y_1033_ = v___x_1220_;
                    v___y_1034_ = v___x_1133_;
                    v___y_1035_ = v___y_1102_;
                    v___y_1036_ = v___x_1135_;
                    v___y_1037_ = v___x_1235_;
                    v___y_1038_ = v___x_1130_;
                    v___y_1039_ = v___x_1124_;
                    v___y_1040_ = v___y_1106_;
                    v___y_1041_ = v___y_1108_;
                    v___y_1042_ = v___y_1111_;
                    v___y_1043_ = v___x_1131_;
                    v___y_1044_ = v___y_1112_;
                    v___y_1045_ = v___y_1114_;
                    v___y_1046_ = v___y_1115_;
                    v___y_1047_ = v___y_1116_;
                    v___y_1048_ = v___x_1142_;
                    v___y_1049_ = v___x_1256_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref_n(v___y_1274_, 2);
                v___x_1276_ = l_Array_append___redArg(v___y_1274_, v___y_1275_);
                lean_dec_ref(v___y_1275_);
                lean_inc_n(v___y_1271_, 5);
                lean_inc_n(v___y_1265_, 18);
                v___x_1277_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1277_, 0, v___y_1265_);
                lean_ctor_set(v___x_1277_, 1, v___y_1271_);
                lean_ctor_set(v___x_1277_, 2, v___x_1276_);
                v___x_1278_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1278_, 0, v___y_1265_);
                lean_ctor_set(v___x_1278_, 1, v___y_1271_);
                lean_ctor_set(v___x_1278_, 2, v___y_1274_);
                v___x_1279_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__70;
                v___x_1280_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__71;
                v___x_1281_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1281_, 0, v___y_1265_);
                lean_ctor_set(v___x_1281_, 1, v___x_1279_);
                v___x_1282_ = l_Lean_Syntax_node1(v___y_1265_, v___x_1280_, v___x_1281_);
                v___x_1283_ = l_Lean_Syntax_node1(v___y_1265_, v___y_1271_, v___x_1282_);
                v___x_1284_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__72;
                v___x_1285_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__73;
                v___x_1286_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1286_, 0, v___y_1265_);
                lean_ctor_set(v___x_1286_, 1, v___x_1284_);
                v___x_1287_ = l_Lean_Syntax_node1(v___y_1265_, v___x_1285_, v___x_1286_);
                v___x_1288_ = l_Lean_Syntax_node1(v___y_1265_, v___y_1271_, v___x_1287_);
                lean_inc(v___x_1288_);
                lean_inc(v___x_1283_);
                lean_inc_ref_n(v___x_1278_, 4);
                lean_inc_ref(v___x_1277_);
                lean_inc(v___y_1259_);
                v___x_1289_ = l_Lean_Syntax_node7(
                    v___y_1265_,
                    v___y_1259_,
                    v___x_1277_,
                    v___x_1278_,
                    v___x_1283_,
                    v___x_1278_,
                    v___x_1288_,
                    v___x_1278_,
                    v___x_1278_,
                );
                v___x_1290_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__75;
                lean_inc_ref(v___y_1263_);
                v___x_1291_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1291_, 0, v___y_1265_);
                lean_ctor_set(v___x_1291_, 1, v___y_1263_);
                v___x_1292_ = l_Lean_Syntax_node1(v___y_1265_, v___x_1290_, v___x_1291_);
                v___x_1293_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__77);
                v___x_1294_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__78;
                lean_inc_n(v___y_1260_, 3);
                lean_inc_n(v___y_1258_, 3);
                v___x_1295_ = l_Lean_addMacroScope(v___y_1258_, v___x_1294_, v___y_1260_);
                v___x_1296_ = lean_box(0);
                v___x_1297_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1297_, 0, v___y_1265_);
                lean_ctor_set(v___x_1297_, 1, v___x_1293_);
                lean_ctor_set(v___x_1297_, 2, v___x_1295_);
                lean_ctor_set(v___x_1297_, 3, v___x_1296_);
                v___x_1298_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__79;
                v___x_1299_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__81;
                v___x_1300_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__82;
                v___x_1301_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1301_, 0, v___y_1265_);
                lean_ctor_set(v___x_1301_, 1, v___x_1300_);
                v___x_1302_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__84);
                v___x_1303_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__85;
                v___x_1304_ = l_Lean_addMacroScope(v___y_1258_, v___x_1303_, v___y_1260_);
                v___x_1305_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__90;
                v___x_1306_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1306_, 0, v___y_1265_);
                lean_ctor_set(v___x_1306_, 1, v___x_1302_);
                lean_ctor_set(v___x_1306_, 2, v___x_1304_);
                lean_ctor_set(v___x_1306_, 3, v___x_1305_);
                lean_inc_ref(v___x_1301_);
                v___x_1307_ =
                    l_Lean_Syntax_node2(v___y_1265_, v___x_1299_, v___x_1301_, v___x_1306_);
                v___x_1308_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__91;
                v___x_1309_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1309_, 0, v___y_1265_);
                lean_ctor_set(v___x_1309_, 1, v___x_1308_);
                lean_inc_ref(v___x_1309_);
                v___x_1310_ = l_Lean_Syntax_node3(
                    v___y_1265_,
                    v___y_1271_,
                    v___x_1297_,
                    v___x_1307_,
                    v___x_1309_,
                );
                v___x_1311_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__93;
                v___x_1312_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__95;
                v___x_1313_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__97;
                v___x_1314_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__99;
                v___x_1315_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__100);
                v___x_1316_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__101;
                v___x_1317_ = l_Lean_addMacroScope(v___y_1258_, v___x_1316_, v___y_1260_);
                v___x_1318_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__104;
                v___x_1319_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1319_, 0, v___y_1265_);
                lean_ctor_set(v___x_1319_, 1, v___x_1315_);
                lean_ctor_set(v___x_1319_, 2, v___x_1317_);
                lean_ctor_set(v___x_1319_, 3, v___x_1318_);
                lean_inc(v___y_1264_);
                v___x_1320_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_1296_,
                    v___y_1264_,
                );
                if lean_obj_tag(v___x_1320_) == 0 {
                    v___x_1321_ = l_Lean_quoteNameMk(v___y_1264_);
                    v___y_1085_ = v___x_1299_;
                    v___y_1086_ = v___x_1277_;
                    v___y_1087_ = v___y_1260_;
                    v___y_1088_ = v___x_1296_;
                    v___y_1089_ = v___y_1261_;
                    v___y_1090_ = v___x_1296_;
                    v___y_1091_ = v___y_1262_;
                    v___y_1092_ = v___x_1292_;
                    v___y_1093_ = v___x_1311_;
                    v___y_1094_ = v___x_1309_;
                    v___y_1095_ = v___y_1265_;
                    v___y_1096_ = v___y_1266_;
                    v___y_1097_ = v___y_1269_;
                    v___y_1098_ = v___x_1278_;
                    v___y_1099_ = v___x_1288_;
                    v___y_1100_ = v___y_1273_;
                    v___y_1101_ = v___x_1314_;
                    v___y_1102_ = v___y_1258_;
                    v___y_1103_ = v___y_1259_;
                    v___y_1104_ = v___x_1283_;
                    v___y_1105_ = v___x_1289_;
                    v___y_1106_ = v___x_1312_;
                    v___y_1107_ = v___x_1310_;
                    v___y_1108_ = v___y_1267_;
                    v___y_1109_ = v___x_1319_;
                    v___y_1110_ = v___y_1268_;
                    v___y_1111_ = v___x_1301_;
                    v___y_1112_ = v___y_1270_;
                    v___y_1113_ = v___x_1298_;
                    v___y_1114_ = v___x_1313_;
                    v___y_1115_ = v___y_1271_;
                    v___y_1116_ = v___y_1272_;
                    v___y_1117_ = v___x_1321_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_1264_);
                    v_val_1322_ = lean_ctor_get(v___x_1320_, 0);
                    lean_inc(v_val_1322_);
                    lean_dec_ref_known(v___x_1320_, 1);
                    v___x_1323_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__105;
                    v___x_1324_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__68;
                    v___x_1325_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__69;
                    v___x_1326_ = lean_string_intercalate(v___x_1325_, v_val_1322_);
                    v___x_1327_ = lean_string_append(v___x_1324_, v___x_1326_);
                    lean_dec_ref(v___x_1326_);
                    lean_inc_n(v___y_1261_, 2);
                    v___x_1328_ = l_Lean_Syntax_mkNameLit(v___x_1327_, v___y_1261_);
                    v___x_1329_ = lean_unsigned_to_nat(1);
                    v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
                    v___x_1331_ = lean_array_push(v___x_1330_, v___x_1328_);
                    v___x_1332_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1332_, 0, v___y_1261_);
                    lean_ctor_set(v___x_1332_, 1, v___x_1323_);
                    lean_ctor_set(v___x_1332_, 2, v___x_1331_);
                    v___y_1085_ = v___x_1299_;
                    v___y_1086_ = v___x_1277_;
                    v___y_1087_ = v___y_1260_;
                    v___y_1088_ = v___x_1296_;
                    v___y_1089_ = v___y_1261_;
                    v___y_1090_ = v___x_1296_;
                    v___y_1091_ = v___y_1262_;
                    v___y_1092_ = v___x_1292_;
                    v___y_1093_ = v___x_1311_;
                    v___y_1094_ = v___x_1309_;
                    v___y_1095_ = v___y_1265_;
                    v___y_1096_ = v___y_1266_;
                    v___y_1097_ = v___y_1269_;
                    v___y_1098_ = v___x_1278_;
                    v___y_1099_ = v___x_1288_;
                    v___y_1100_ = v___y_1273_;
                    v___y_1101_ = v___x_1314_;
                    v___y_1102_ = v___y_1258_;
                    v___y_1103_ = v___y_1259_;
                    v___y_1104_ = v___x_1283_;
                    v___y_1105_ = v___x_1289_;
                    v___y_1106_ = v___x_1312_;
                    v___y_1107_ = v___x_1310_;
                    v___y_1108_ = v___y_1267_;
                    v___y_1109_ = v___x_1319_;
                    v___y_1110_ = v___y_1268_;
                    v___y_1111_ = v___x_1301_;
                    v___y_1112_ = v___y_1270_;
                    v___y_1113_ = v___x_1298_;
                    v___y_1114_ = v___x_1313_;
                    v___y_1115_ = v___y_1271_;
                    v___y_1116_ = v___y_1272_;
                    v___y_1117_ = v___x_1332_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_quotContext_1349_ = lean_ctor_get(v_a_1010_, 1);
                v_currMacroScope_1350_ = lean_ctor_get(v_a_1010_, 2);
                v_ref_1351_ = lean_ctor_get(v_a_1010_, 5);
                v___x_1352_ = l_String_removeLeadingSpaces(v___y_1348_);
                v___x_1353_ = lean_box(2);
                v___x_1354_ = l_Lean_Syntax_mkStrLit(v___x_1352_, v___x_1353_);
                lean_inc(v___y_1342_);
                v___x_1355_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v___y_1342_);
                v_procId_1356_ = l_Lean_mkIdentFrom(v_id_1340_, v___x_1355_, v___y_1344_);
                lean_dec(v_id_1340_);
                v___x_1357_ = l_Lean_TSyntax_getId(v_procId_1356_);
                lean_inc_n(v___x_1357_, 2);
                v_procStr_1358_ = l_Lean_Name_toString(v___x_1357_, v___x_1334_);
                v___x_1359_ = l_Lean_Name_append(v___y_1343_, v___x_1357_);
                v_procIdParser_1360_ = l_Lean_mkIdentFrom(v_procId_1356_, v___x_1359_, v___y_1344_);
                lean_dec(v_procId_1356_);
                v___x_1361_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__106;
                v___x_1362_ = lean_string_append(v___x_1361_, v_procStr_1358_);
                v___x_1363_ = l_Lean_Syntax_mkStrLit(v___x_1362_, v___x_1353_);
                v___x_1364_ = l_Lean_SourceInfo_fromRef(v_ref_1351_, v___y_1344_);
                v___x_1365_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__108;
                v___x_1366_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__109;
                v___x_1367_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__110;
                v___x_1368_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__112;
                v___x_1369_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113), core::ptr::addr_of_mut!(l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113_once), _init_l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__113);
                if lean_obj_tag(v___y_1347_) == 1 {
                    v_val_1370_ = lean_ctor_get(v___y_1347_, 0);
                    lean_inc(v_val_1370_);
                    lean_dec_ref_known(v___y_1347_, 1);
                    v___x_1371_ = l_Array_mkArray1___redArg(v_val_1370_);
                    v___y_1258_ = v_quotContext_1349_;
                    v___y_1259_ = v___x_1368_;
                    v___y_1260_ = v_currMacroScope_1350_;
                    v___y_1261_ = v___x_1353_;
                    v___y_1262_ = v___x_1357_;
                    v___y_1263_ = v___x_1366_;
                    v___y_1264_ = v___y_1342_;
                    v___y_1265_ = v___x_1364_;
                    v___y_1266_ = v_procIdParser_1360_;
                    v___y_1267_ = v___x_1367_;
                    v___y_1268_ = v___y_1346_;
                    v___y_1269_ = v___y_1345_;
                    v___y_1270_ = v___x_1363_;
                    v___y_1271_ = v___x_1365_;
                    v___y_1272_ = v_procStr_1358_;
                    v___y_1273_ = v___x_1354_;
                    v___y_1274_ = v___x_1369_;
                    v___y_1275_ = v___x_1371_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_1347_);
                    v___x_1372_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__114;
                    v___y_1258_ = v_quotContext_1349_;
                    v___y_1259_ = v___x_1368_;
                    v___y_1260_ = v_currMacroScope_1350_;
                    v___y_1261_ = v___x_1353_;
                    v___y_1262_ = v___x_1357_;
                    v___y_1263_ = v___x_1366_;
                    v___y_1264_ = v___y_1342_;
                    v___y_1265_ = v___x_1364_;
                    v___y_1266_ = v_procIdParser_1360_;
                    v___y_1267_ = v___x_1367_;
                    v___y_1268_ = v___y_1346_;
                    v___y_1269_ = v___y_1345_;
                    v___y_1270_ = v___x_1363_;
                    v___y_1271_ = v___x_1365_;
                    v___y_1272_ = v_procStr_1358_;
                    v___y_1273_ = v___x_1354_;
                    v___y_1274_ = v___x_1369_;
                    v___y_1275_ = v___x_1372_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_1375_ = l_Lean_TSyntax_getId(v_id_1340_);
                lean_inc_n(v___x_1375_, 2);
                v_str_1376_ = l_Lean_Name_toString(v___x_1375_, v___x_1334_);
                v___x_1377_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__116;
                v___x_1378_ = l_Lean_Name_append(v___x_1377_, v___x_1375_);
                v___x_1379_ = 0;
                v_idParser_1380_ = l_Lean_mkIdentFrom(v_id_1340_, v___x_1378_, v___x_1379_);
                if lean_obj_tag(v___y_1374_) == 0 {
                    v___x_1381_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___closed__117;
                    v___x_1382_ = lean_string_append(v___x_1381_, v_str_1376_);
                    v___y_1342_ = v___x_1375_;
                    v___y_1343_ = v___x_1377_;
                    v___y_1344_ = v___x_1379_;
                    v___y_1345_ = v_str_1376_;
                    v___y_1346_ = v_idParser_1380_;
                    v___y_1347_ = v___y_1374_;
                    v___y_1348_ = v___x_1382_;
                    state = 4;
                    continue;
                } else {
                    v_val_1383_ = lean_ctor_get(v___y_1374_, 0);
                    v___x_1384_ = l_Lean_TSyntax_getDocString(v_val_1383_);
                    v___y_1342_ = v___x_1375_;
                    v___y_1343_ = v___x_1377_;
                    v___y_1344_ = v___x_1379_;
                    v___y_1345_ = v_str_1376_;
                    v___y_1346_ = v_idParser_1380_;
                    v___y_1347_ = v___y_1374_;
                    v___y_1348_ = v___x_1384_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_1390_ == 0 {
                    v___x_1392_ = v___x_1389_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1387_);
                    v___x_1392_ = v_reuseFailAlloc_1393_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1374_ = v___x_1392_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1___boxed(
    mut v_x_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1398_: *mut LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Lean_Meta_Simp___aux__Lean__Meta__Tactic__Simp__RegisterCommand______macroRules__Lean__Meta__Simp____root____Lean__Parser__Command__registerSimpAttr__1(v_x_1395_, v_a_1396_, v_a_1397_);
    lean_dec_ref(v_a_1396_);
    return v_res_1398_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
}

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RegisterCommand
// Imports: Lean.Meta.Tactic.Grind.Attr
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom, l_Lean_quoteNameMk,
    lean_name_append_after,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr8, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::{
    initialize_Lean_Meta_Tactic_Grind_Attr, meta_initialize_Lean_Meta_Tactic_Grind_Attr,
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
pub static l_Lean_Parser_Command_registerGrindAttr___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__1_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__2_value: LeanStringObject<6> =
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
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__3_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__4_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__5_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__6_value: LeanStringObject<18> =
    LeanStringObject {
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
            114, 101, 103, 105, 115, 116, 101, 114, 71, 114, 105, 110, 100, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__6_value)
        as *mut LeanObject;
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__2_value)
                as *mut LeanObject,
            15218882539576375456 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__3_value)
                as *mut LeanObject,
            10894953475799083135 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_4: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value)
                as *mut LeanObject,
            16768254041580879794 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_5: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_4)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value)
                as *mut LeanObject,
            9258084944359107691 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_6: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_5)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value)
                as *mut LeanObject,
            12321285108252463578 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_registerGrindAttr___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value_aux_6)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__6_value)
                as *mut LeanObject,
            8671985483701543741 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__8_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__8_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__10_value: LeanStringObject<9> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__10_value)
                as *mut LeanObject,
            18170484695678750185 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__12_value: LeanStringObject<11> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__12_value)
                as *mut LeanObject,
            3961966953292576997 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__15_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__16_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            114, 101, 103, 105, 115, 116, 101, 114, 95, 103, 114, 105, 110, 100, 95, 97, 116, 116,
            114, 0,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__19_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Command_registerGrindAttr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__19_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__21_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__22_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__21_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Command_registerGrindAttr___closed__23_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__7_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_registerGrindAttr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__23_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Command_registerGrindAttr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0_value) as *mut LeanObject,2812521669163367463 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__3_value) as *mut LeanObject,17682753938374962505 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 111, 109, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__10_value) as *mut LeanObject,6376237424612349584 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 120, 95, 63, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__12_value) as *mut LeanObject,14916367973757185555 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__14_value) as *mut LeanObject,14182491107802134955 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 97, 116, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__9_value) as *mut LeanObject,1765827125244227832 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__16_value) as *mut LeanObject,14125453249386077023 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 112, 83, 112, 97, 99, 101, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18_value) as *mut LeanObject,17761616517784022991 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 65, 116, 116, 114, 46, 103, 114, 105, 110, 100, 77, 111, 100, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 114, 105, 110, 100, 77, 111, 100, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24_value) as *mut LeanObject,6289677862665402693 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27_value) as *mut LeanObject,10411423847645546083 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29_value) as *mut LeanObject,4787239732180154236 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__31_value) as *mut LeanObject,387456110215466097 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33_value) as *mut LeanObject,6455343056875556081 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__37_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value) as *mut LeanObject,78276241817253953 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__2_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40_value) as *mut LeanObject,11064967765627998686 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__43_value) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__45_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__44_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__46_value) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__49_value) as *mut LeanObject,3326968124746134365 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__51_value) as *mut LeanObject,940684074193935882 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__53_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__55_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 103, 105, 115, 116, 101, 114, 65, 116, 116, 114, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value) as *mut LeanObject,3089151217792981346 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__2_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57_value) as *mut LeanObject,13100527433736655829 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__60_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__61_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__63_value) as *mut LeanObject,9368229134555052249 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67_value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [33, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [33, 63, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__72_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74_value) as *mut LeanObject,12014440461648055863 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value) as *mut LeanObject;
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__4_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerGrindAttr___closed__5_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__76_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19()
-> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__18;
    v___x_596_ = l_String_toRawSubstring_x27(v___x_595_);
    return v___x_596_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22()
-> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__21;
    v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
    return v___x_601_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25()
-> *mut LeanObject {
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    v___x_604_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__24;
    v___x_605_ = l_String_toRawSubstring_x27(v___x_604_);
    return v___x_605_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34()
-> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__33;
    v___x_628_ = l_String_toRawSubstring_x27(v___x_627_);
    return v___x_628_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41()
-> *mut LeanObject {
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__40;
    v___x_641_ = l_String_toRawSubstring_x27(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58()
-> *mut LeanObject {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__57;
    v___x_687_ = l_String_toRawSubstring_x27(v___x_686_);
    return v___x_687_;
}
pub unsafe fn _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78()
-> *mut LeanObject {
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Array_mkArray0(lean_box(0));
    return v___x_732_;
}
pub unsafe fn l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(
    mut v_x_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_770_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str1_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v_idParser1_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str2_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idParser2_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str3_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idParser3_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str4_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idParser4_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_738_ = l_Lean_Parser_Command_registerGrindAttr___closed__0;
                v___x_739_ = l_Lean_Parser_Command_registerGrindAttr___closed__4;
                v___x_951_ = l_Lean_Parser_Command_registerGrindAttr___closed__7;
                lean_inc(v_x_735_);
                v___x_952_ = l_Lean_Syntax_isOfKind(v_x_735_, v___x_951_);
                if v___x_952_ == 0 {
                    lean_dec(v_x_735_);
                    v___x_953_ = lean_box(1);
                    v___x_954_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_954_, 0, v___x_953_);
                    lean_ctor_set(v___x_954_, 1, v_a_737_);
                    return v___x_954_;
                } else {
                    v___x_955_ = lean_unsigned_to_nat(0);
                    v___x_956_ = l_Lean_Syntax_getArg(v_x_735_, v___x_955_);
                    v___x_957_ = lean_unsigned_to_nat(2);
                    v_id_958_ = l_Lean_Syntax_getArg(v_x_735_, v___x_957_);
                    lean_dec(v_x_735_);
                    v___x_995_ = l_Lean_Syntax_getOptional_x3f(v___x_956_);
                    lean_dec(v___x_956_);
                    if lean_obj_tag(v___x_995_) == 0 {
                        v___x_996_ = lean_box(0);
                        v___y_960_ = v___x_996_;
                        state = 3;
                        continue;
                    } else {
                        v_val_997_ = lean_ctor_get(v___x_995_, 0);
                        v_isSharedCheck_1004_ = (!lean_is_exclusive(v___x_995_)) as u8;
                        if v_isSharedCheck_1004_ == 0 {
                            v___x_999_ = v___x_995_;
                            v_isShared_1000_ = v_isSharedCheck_1004_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_997_);
                            lean_dec(v___x_995_);
                            v___x_999_ = lean_box(0);
                            v_isShared_1000_ = v_isSharedCheck_1004_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_n(v___y_763_, 12);
                lean_inc_n(v___y_759_, 42);
                v___x_771_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___y_770_);
                lean_inc(v___y_767_);
                v___x_772_ = l_Lean_Syntax_node2(v___y_759_, v___y_767_, v___y_744_, v___x_771_);
                lean_inc(v___y_742_);
                v___x_773_ = l_Lean_Syntax_node1(v___y_759_, v___y_742_, v___x_772_);
                lean_inc_n(v___y_753_, 9);
                lean_inc(v___y_741_);
                v___x_774_ = l_Lean_Syntax_node2(v___y_759_, v___y_741_, v___x_773_, v___y_753_);
                v___x_775_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___x_774_);
                lean_inc(v___y_764_);
                v___x_776_ = l_Lean_Syntax_node1(v___y_759_, v___y_764_, v___x_775_);
                lean_inc(v___y_748_);
                v___x_777_ = l_Lean_Syntax_node4(
                    v___y_759_, v___y_748_, v___y_747_, v___y_762_, v___y_758_, v___x_776_,
                );
                v___x_778_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__0;
                v___x_779_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__1;
                v___x_780_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__2;
                lean_inc_ref(v___y_743_);
                v___x_781_ = l_Lean_Name_mkStr4(v___x_738_, v___x_739_, v___y_743_, v___x_780_);
                v___x_782_ = l_Lean_Syntax_node1(v___y_759_, v___x_781_, v___y_753_);
                v___x_783_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_783_, 0, v___y_759_);
                lean_ctor_set(v___x_783_, 1, v___x_778_);
                v___x_784_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__4;
                v___x_785_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__5;
                v___x_786_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_786_, 0, v___y_759_);
                lean_ctor_set(v___x_786_, 1, v___x_785_);
                v___x_787_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__6;
                v___x_788_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_788_, 0, v___y_759_);
                lean_ctor_set(v___x_788_, 1, v___x_787_);
                v___x_789_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__7;
                v___x_790_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_790_, 0, v___y_759_);
                lean_ctor_set(v___x_790_, 1, v___x_789_);
                v___x_791_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__8;
                v___x_792_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_792_, 0, v___y_759_);
                lean_ctor_set(v___x_792_, 1, v___x_791_);
                lean_inc_ref_n(v___x_792_, 4);
                lean_inc_ref_n(v___x_790_, 3);
                lean_inc_ref_n(v___x_788_, 3);
                lean_inc_ref_n(v___x_786_, 4);
                v___x_793_ = l_Lean_Syntax_node5(
                    v___y_759_, v___x_784_, v___x_786_, v___x_788_, v___x_790_, v___y_769_,
                    v___x_792_,
                );
                v___x_794_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___x_793_);
                v___x_795_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__11;
                v___x_796_ = lean_box(2);
                v___x_797_ = l_Lean_Syntax_mkStrLit(v___y_752_, v___x_796_);
                v___x_798_ = l_Lean_Syntax_node1(v___y_759_, v___x_795_, v___x_797_);
                v___x_799_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__13;
                v___x_800_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__15;
                v___x_801_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__17;
                v___x_802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__19);
                v___x_803_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__20;
                lean_inc_n(v___y_766_, 3);
                lean_inc_n(v___y_749_, 3);
                v___x_804_ = l_Lean_addMacroScope(v___y_749_, v___x_803_, v___y_766_);
                lean_inc_n(v___y_760_, 2);
                v___x_805_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_805_, 0, v___y_759_);
                lean_ctor_set(v___x_805_, 1, v___x_802_);
                lean_ctor_set(v___x_805_, 2, v___x_804_);
                lean_ctor_set(v___x_805_, 3, v___y_760_);
                v___x_806_ = l_Lean_Syntax_node2(v___y_759_, v___x_801_, v___x_805_, v___y_753_);
                v___x_807_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__22);
                v___x_808_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__23;
                lean_inc_ref(v___y_757_);
                v___x_809_ = l_Lean_Name_mkStr4(v___x_738_, v___x_739_, v___y_757_, v___x_808_);
                lean_inc(v___x_809_);
                v___x_810_ = l_Lean_addMacroScope(v___y_749_, v___x_809_, v___y_766_);
                v___x_811_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_811_, 0, v___x_809_);
                lean_ctor_set(v___x_811_, 1, v___y_750_);
                v___x_812_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_812_, 0, v___x_811_);
                lean_ctor_set(v___x_812_, 1, v___y_760_);
                v___x_813_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_813_, 0, v___y_759_);
                lean_ctor_set(v___x_813_, 1, v___x_807_);
                lean_ctor_set(v___x_813_, 2, v___x_810_);
                lean_ctor_set(v___x_813_, 3, v___x_812_);
                v___x_814_ = l_Lean_Syntax_node2(v___y_759_, v___x_801_, v___x_813_, v___y_753_);
                v___x_815_ = l_Lean_Syntax_node2(v___y_759_, v___y_763_, v___x_806_, v___x_814_);
                v___x_816_ =
                    l_Lean_Syntax_node3(v___y_759_, v___x_800_, v___x_786_, v___x_815_, v___x_792_);
                v___x_817_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_817_, 0, v___y_759_);
                lean_ctor_set(v___x_817_, 1, v___y_745_);
                v___x_818_ = l_Lean_Syntax_node2(v___y_759_, v___x_799_, v___x_816_, v___x_817_);
                lean_inc_n(v___x_818_, 3);
                v___x_819_ = l_Lean_Syntax_node2(v___y_759_, v___y_763_, v___x_798_, v___x_818_);
                v___x_820_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__25);
                v___x_821_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__26;
                v___x_822_ = l_Lean_addMacroScope(v___y_749_, v___x_821_, v___y_766_);
                v___x_823_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_823_, 0, v___y_759_);
                lean_ctor_set(v___x_823_, 1, v___x_820_);
                lean_ctor_set(v___x_823_, 2, v___x_822_);
                lean_ctor_set(v___x_823_, 3, v___y_760_);
                v___x_824_ = lean_unsigned_to_nat(10);
                v___x_825_ = lean_mk_empty_array_with_capacity(v___x_824_);
                v___x_826_ = lean_array_push(v___x_825_, v___y_756_);
                v___x_827_ = lean_array_push(v___x_826_, v___y_753_);
                v___x_828_ = lean_array_push(v___x_827_, v___x_782_);
                v___x_829_ = lean_array_push(v___x_828_, v___x_783_);
                v___x_830_ = lean_array_push(v___x_829_, v___y_753_);
                lean_inc_ref_n(v___x_830_, 3);
                v___x_831_ = lean_array_push(v___x_830_, v___x_794_);
                v___x_832_ = lean_array_push(v___x_831_, v___y_753_);
                v___x_833_ = lean_array_push(v___x_832_, v___x_819_);
                lean_inc_n(v___y_746_, 3);
                v___x_834_ = lean_array_push(v___x_833_, v___y_746_);
                lean_inc_ref_n(v___x_823_, 3);
                v___x_835_ = lean_array_push(v___x_834_, v___x_823_);
                v___x_836_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_836_, 0, v___y_759_);
                lean_ctor_set(v___x_836_, 1, v___x_779_);
                lean_ctor_set(v___x_836_, 2, v___x_835_);
                v___x_837_ = l_Lean_Syntax_node5(
                    v___y_759_, v___x_784_, v___x_786_, v___x_788_, v___x_790_, v___y_761_,
                    v___x_792_,
                );
                v___x_838_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___x_837_);
                v___x_839_ = l_Lean_Syntax_mkStrLit(v___y_751_, v___x_796_);
                v___x_840_ = l_Lean_Syntax_node1(v___y_759_, v___x_795_, v___x_839_);
                v___x_841_ = l_Lean_Syntax_node2(v___y_759_, v___y_763_, v___x_840_, v___x_818_);
                v___x_842_ = lean_array_push(v___x_830_, v___x_838_);
                v___x_843_ = lean_array_push(v___x_842_, v___y_753_);
                v___x_844_ = lean_array_push(v___x_843_, v___x_841_);
                v___x_845_ = lean_array_push(v___x_844_, v___y_746_);
                v___x_846_ = lean_array_push(v___x_845_, v___x_823_);
                v___x_847_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_847_, 0, v___y_759_);
                lean_ctor_set(v___x_847_, 1, v___x_779_);
                lean_ctor_set(v___x_847_, 2, v___x_846_);
                v___x_848_ = l_Lean_Syntax_node5(
                    v___y_759_, v___x_784_, v___x_786_, v___x_788_, v___x_790_, v___y_768_,
                    v___x_792_,
                );
                v___x_849_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___x_848_);
                v___x_850_ = l_Lean_Syntax_mkStrLit(v___y_755_, v___x_796_);
                v___x_851_ = l_Lean_Syntax_node1(v___y_759_, v___x_795_, v___x_850_);
                v___x_852_ = l_Lean_Syntax_node2(v___y_759_, v___y_763_, v___x_851_, v___x_818_);
                v___x_853_ = lean_array_push(v___x_830_, v___x_849_);
                v___x_854_ = lean_array_push(v___x_853_, v___y_753_);
                v___x_855_ = lean_array_push(v___x_854_, v___x_852_);
                v___x_856_ = lean_array_push(v___x_855_, v___y_746_);
                v___x_857_ = lean_array_push(v___x_856_, v___x_823_);
                v___x_858_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_858_, 0, v___y_759_);
                lean_ctor_set(v___x_858_, 1, v___x_779_);
                lean_ctor_set(v___x_858_, 2, v___x_857_);
                v___x_859_ = l_Lean_Syntax_node5(
                    v___y_759_, v___x_784_, v___x_786_, v___x_788_, v___x_790_, v___y_765_,
                    v___x_792_,
                );
                v___x_860_ = l_Lean_Syntax_node1(v___y_759_, v___y_763_, v___x_859_);
                v___x_861_ = l_Lean_Syntax_mkStrLit(v___y_754_, v___x_796_);
                v___x_862_ = l_Lean_Syntax_node1(v___y_759_, v___x_795_, v___x_861_);
                v___x_863_ = l_Lean_Syntax_node2(v___y_759_, v___y_763_, v___x_862_, v___x_818_);
                v___x_864_ = lean_array_push(v___x_830_, v___x_860_);
                v___x_865_ = lean_array_push(v___x_864_, v___y_753_);
                v___x_866_ = lean_array_push(v___x_865_, v___x_863_);
                v___x_867_ = lean_array_push(v___x_866_, v___y_746_);
                v___x_868_ = lean_array_push(v___x_867_, v___x_823_);
                v___x_869_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_869_, 0, v___y_759_);
                lean_ctor_set(v___x_869_, 1, v___x_779_);
                lean_ctor_set(v___x_869_, 2, v___x_868_);
                v___x_870_ = l_Lean_Syntax_node5(
                    v___y_759_, v___y_763_, v___x_777_, v___x_836_, v___x_847_, v___x_858_,
                    v___x_869_,
                );
                v___x_871_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_871_, 0, v___x_870_);
                lean_ctor_set(v___x_871_, 1, v_a_737_);
                return v___x_871_;
            }
            2 => {
                lean_inc_ref_n(v___y_886_, 2);
                v___x_893_ = l_Array_append___redArg(v___y_886_, v___y_892_);
                lean_dec_ref(v___y_892_);
                lean_inc_n(v___y_882_, 5);
                lean_inc_n(v___y_880_, 18);
                v___x_894_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_894_, 0, v___y_880_);
                lean_ctor_set(v___x_894_, 1, v___y_882_);
                lean_ctor_set(v___x_894_, 2, v___x_893_);
                v___x_895_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_895_, 0, v___y_880_);
                lean_ctor_set(v___x_895_, 1, v___y_882_);
                lean_ctor_set(v___x_895_, 2, v___y_886_);
                v___x_896_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__27;
                v___x_897_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__28;
                v___x_898_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_898_, 0, v___y_880_);
                lean_ctor_set(v___x_898_, 1, v___x_896_);
                v___x_899_ = l_Lean_Syntax_node1(v___y_880_, v___x_897_, v___x_898_);
                v___x_900_ = l_Lean_Syntax_node1(v___y_880_, v___y_882_, v___x_899_);
                v___x_901_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__29;
                v___x_902_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__30;
                v___x_903_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_903_, 0, v___y_880_);
                lean_ctor_set(v___x_903_, 1, v___x_901_);
                v___x_904_ = l_Lean_Syntax_node1(v___y_880_, v___x_902_, v___x_903_);
                v___x_905_ = l_Lean_Syntax_node1(v___y_880_, v___y_882_, v___x_904_);
                lean_inc_ref_n(v___x_895_, 4);
                lean_inc_ref(v___x_894_);
                lean_inc(v___y_878_);
                v___x_906_ = l_Lean_Syntax_node7(
                    v___y_880_, v___y_878_, v___x_894_, v___x_895_, v___x_900_, v___x_895_,
                    v___x_905_, v___x_895_, v___x_895_,
                );
                v___x_907_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__32;
                lean_inc_ref(v___y_889_);
                v___x_908_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_908_, 0, v___y_880_);
                lean_ctor_set(v___x_908_, 1, v___y_889_);
                v___x_909_ = l_Lean_Syntax_node1(v___y_880_, v___x_907_, v___x_908_);
                v___x_910_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__34);
                v___x_911_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__35;
                lean_inc_n(v___y_887_, 3);
                lean_inc_n(v___y_884_, 3);
                v___x_912_ = l_Lean_addMacroScope(v___y_884_, v___x_911_, v___y_887_);
                v___x_913_ = lean_box(0);
                v___x_914_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_914_, 0, v___y_880_);
                lean_ctor_set(v___x_914_, 1, v___x_910_);
                lean_ctor_set(v___x_914_, 2, v___x_912_);
                lean_ctor_set(v___x_914_, 3, v___x_913_);
                v___x_915_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__36;
                v___x_916_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__38;
                v___x_917_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__39;
                v___x_918_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_918_, 0, v___y_880_);
                lean_ctor_set(v___x_918_, 1, v___x_917_);
                v___x_919_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__41);
                v___x_920_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__42;
                v___x_921_ = l_Lean_addMacroScope(v___y_884_, v___x_920_, v___y_887_);
                v___x_922_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__47;
                v___x_923_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_923_, 0, v___y_880_);
                lean_ctor_set(v___x_923_, 1, v___x_919_);
                lean_ctor_set(v___x_923_, 2, v___x_921_);
                lean_ctor_set(v___x_923_, 3, v___x_922_);
                lean_inc_ref(v___x_918_);
                v___x_924_ = l_Lean_Syntax_node2(v___y_880_, v___x_916_, v___x_918_, v___x_923_);
                v___x_925_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__48;
                v___x_926_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_926_, 0, v___y_880_);
                lean_ctor_set(v___x_926_, 1, v___x_925_);
                v___x_927_ =
                    l_Lean_Syntax_node3(v___y_880_, v___y_882_, v___x_914_, v___x_924_, v___x_926_);
                v___x_928_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__50;
                v___x_929_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__52;
                v___x_930_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__54;
                v___x_931_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__56;
                v___x_932_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__58);
                v___x_933_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__59;
                v___x_934_ = l_Lean_addMacroScope(v___y_884_, v___x_933_, v___y_887_);
                v___x_935_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__62;
                v___x_936_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_936_, 0, v___y_880_);
                lean_ctor_set(v___x_936_, 1, v___x_932_);
                lean_ctor_set(v___x_936_, 2, v___x_934_);
                lean_ctor_set(v___x_936_, 3, v___x_935_);
                lean_inc(v___y_874_);
                v___x_937_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_913_, v___y_874_,
                );
                if lean_obj_tag(v___x_937_) == 0 {
                    v___x_938_ = l_Lean_quoteNameMk(v___y_874_);
                    v___y_741_ = v___x_929_;
                    v___y_742_ = v___x_930_;
                    v___y_743_ = v___x_915_;
                    v___y_744_ = v___x_936_;
                    v___y_745_ = v___y_879_;
                    v___y_746_ = v___x_918_;
                    v___y_747_ = v___x_906_;
                    v___y_748_ = v___y_883_;
                    v___y_749_ = v___y_884_;
                    v___y_750_ = v___x_913_;
                    v___y_751_ = v___y_888_;
                    v___y_752_ = v___y_873_;
                    v___y_753_ = v___x_895_;
                    v___y_754_ = v___y_875_;
                    v___y_755_ = v___y_876_;
                    v___y_756_ = v___x_894_;
                    v___y_757_ = v___y_877_;
                    v___y_758_ = v___x_927_;
                    v___y_759_ = v___y_880_;
                    v___y_760_ = v___x_913_;
                    v___y_761_ = v___y_881_;
                    v___y_762_ = v___x_909_;
                    v___y_763_ = v___y_882_;
                    v___y_764_ = v___x_928_;
                    v___y_765_ = v___y_885_;
                    v___y_766_ = v___y_887_;
                    v___y_767_ = v___x_931_;
                    v___y_768_ = v___y_891_;
                    v___y_769_ = v___y_890_;
                    v___y_770_ = v___x_938_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_874_);
                    v_val_939_ = lean_ctor_get(v___x_937_, 0);
                    lean_inc(v_val_939_);
                    lean_dec_ref_known(v___x_937_, 1);
                    v___x_940_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__64;
                    v___x_941_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__65;
                    v___x_942_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__66;
                    v___x_943_ = lean_string_intercalate(v___x_942_, v_val_939_);
                    v___x_944_ = lean_string_append(v___x_941_, v___x_943_);
                    lean_dec_ref(v___x_943_);
                    v___x_945_ = lean_box(2);
                    v___x_946_ = l_Lean_Syntax_mkNameLit(v___x_944_, v___x_945_);
                    v___x_947_ = lean_unsigned_to_nat(1);
                    v___x_948_ = lean_mk_empty_array_with_capacity(v___x_947_);
                    v___x_949_ = lean_array_push(v___x_948_, v___x_946_);
                    v___x_950_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_950_, 0, v___x_945_);
                    lean_ctor_set(v___x_950_, 1, v___x_940_);
                    lean_ctor_set(v___x_950_, 2, v___x_949_);
                    v___y_741_ = v___x_929_;
                    v___y_742_ = v___x_930_;
                    v___y_743_ = v___x_915_;
                    v___y_744_ = v___x_936_;
                    v___y_745_ = v___y_879_;
                    v___y_746_ = v___x_918_;
                    v___y_747_ = v___x_906_;
                    v___y_748_ = v___y_883_;
                    v___y_749_ = v___y_884_;
                    v___y_750_ = v___x_913_;
                    v___y_751_ = v___y_888_;
                    v___y_752_ = v___y_873_;
                    v___y_753_ = v___x_895_;
                    v___y_754_ = v___y_875_;
                    v___y_755_ = v___y_876_;
                    v___y_756_ = v___x_894_;
                    v___y_757_ = v___y_877_;
                    v___y_758_ = v___x_927_;
                    v___y_759_ = v___y_880_;
                    v___y_760_ = v___x_913_;
                    v___y_761_ = v___y_881_;
                    v___y_762_ = v___x_909_;
                    v___y_763_ = v___y_882_;
                    v___y_764_ = v___x_928_;
                    v___y_765_ = v___y_885_;
                    v___y_766_ = v___y_887_;
                    v___y_767_ = v___x_931_;
                    v___y_768_ = v___y_891_;
                    v___y_769_ = v___y_890_;
                    v___y_770_ = v___x_950_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_961_ = l_Lean_TSyntax_getId(v_id_958_);
                lean_inc_n(v___x_961_, 5);
                v_str1_962_ = l_Lean_Name_toString(v___x_961_, v___x_952_);
                v___x_963_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__67;
                v___x_964_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__68;
                v___x_965_ = l_Lean_Name_append(v___x_964_, v___x_961_);
                v___x_966_ = 0;
                v_idParser1_967_ = l_Lean_mkIdentFrom(v_id_958_, v___x_965_, v___x_966_);
                v___x_968_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__69;
                lean_inc_ref_n(v_str1_962_, 3);
                v_str2_969_ = lean_string_append(v_str1_962_, v___x_968_);
                v___x_970_ = lean_name_append_after(v___x_961_, v___x_968_);
                v___x_971_ = l_Lean_Name_append(v___x_964_, v___x_970_);
                v_idParser2_972_ = l_Lean_mkIdentFrom(v_id_958_, v___x_971_, v___x_966_);
                v___x_973_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__70;
                v_str3_974_ = lean_string_append(v_str1_962_, v___x_973_);
                v_quotContext_975_ = lean_ctor_get(v_a_736_, 1);
                v_currMacroScope_976_ = lean_ctor_get(v_a_736_, 2);
                v_ref_977_ = lean_ctor_get(v_a_736_, 5);
                v___x_978_ = lean_name_append_after(v___x_961_, v___x_973_);
                v___x_979_ = l_Lean_Name_append(v___x_964_, v___x_978_);
                v_idParser3_980_ = l_Lean_mkIdentFrom(v_id_958_, v___x_979_, v___x_966_);
                v___x_981_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__71;
                v_str4_982_ = lean_string_append(v_str1_962_, v___x_981_);
                v___x_983_ = lean_name_append_after(v___x_961_, v___x_981_);
                v___x_984_ = l_Lean_Name_append(v___x_964_, v___x_983_);
                v_idParser4_985_ = l_Lean_mkIdentFrom(v_id_958_, v___x_984_, v___x_966_);
                lean_dec(v_id_958_);
                v___x_986_ = l_Lean_SourceInfo_fromRef(v_ref_977_, v___x_966_);
                v___x_987_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__73;
                v___x_988_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__74;
                v___x_989_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__75;
                v___x_990_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__77;
                v___x_991_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78), core::ptr::addr_of_mut!(l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78_once), _init_l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__78);
                if lean_obj_tag(v___y_960_) == 1 {
                    v_val_992_ = lean_ctor_get(v___y_960_, 0);
                    lean_inc(v_val_992_);
                    lean_dec_ref_known(v___y_960_, 1);
                    v___x_993_ = l_Array_mkArray1___redArg(v_val_992_);
                    v___y_873_ = v_str1_962_;
                    v___y_874_ = v___x_961_;
                    v___y_875_ = v_str4_982_;
                    v___y_876_ = v_str3_974_;
                    v___y_877_ = v___x_963_;
                    v___y_878_ = v___x_990_;
                    v___y_879_ = v___x_973_;
                    v___y_880_ = v___x_986_;
                    v___y_881_ = v_idParser2_972_;
                    v___y_882_ = v___x_987_;
                    v___y_883_ = v___x_989_;
                    v___y_884_ = v_quotContext_975_;
                    v___y_885_ = v_idParser4_985_;
                    v___y_886_ = v___x_991_;
                    v___y_887_ = v_currMacroScope_976_;
                    v___y_888_ = v_str2_969_;
                    v___y_889_ = v___x_988_;
                    v___y_890_ = v_idParser1_967_;
                    v___y_891_ = v_idParser3_980_;
                    v___y_892_ = v___x_993_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_960_);
                    v___x_994_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___closed__79;
                    v___y_873_ = v_str1_962_;
                    v___y_874_ = v___x_961_;
                    v___y_875_ = v_str4_982_;
                    v___y_876_ = v_str3_974_;
                    v___y_877_ = v___x_963_;
                    v___y_878_ = v___x_990_;
                    v___y_879_ = v___x_973_;
                    v___y_880_ = v___x_986_;
                    v___y_881_ = v_idParser2_972_;
                    v___y_882_ = v___x_987_;
                    v___y_883_ = v___x_989_;
                    v___y_884_ = v_quotContext_975_;
                    v___y_885_ = v_idParser4_985_;
                    v___y_886_ = v___x_991_;
                    v___y_887_ = v_currMacroScope_976_;
                    v___y_888_ = v_str2_969_;
                    v___y_889_ = v___x_988_;
                    v___y_890_ = v_idParser1_967_;
                    v___y_891_ = v_idParser3_980_;
                    v___y_892_ = v___x_994_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_1000_ == 0 {
                    v___x_1002_ = v___x_999_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_997_);
                    v___x_1002_ = v_reuseFailAlloc_1003_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_960_ = v___x_1002_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1___boxed(
    mut v_x_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
    mut v_a_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Meta_Grind___aux__Lean__Meta__Tactic__Grind__RegisterCommand______macroRules__Lean__Meta__Grind____root____Lean__Parser__Command__registerGrindAttr__1(v_x_1005_, v_a_1006_, v_a_1007_);
    lean_dec_ref(v_a_1006_);
    return v_res_1008_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
}

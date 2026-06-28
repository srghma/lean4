// Lean compiler output
// Module: Init.CbvSimproc
// Imports: Init.Data.ToString.Name Init.Tactics Init.Meta.Defs
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, meta_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Syntax_isNone, lean_mk_syntax_ident,
    runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_Syntax_node8,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_cbvSimprocEval___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 69, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__1_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_cbvSimprocEval___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Parser_cbvSimprocEval___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_cbvSimprocEval___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value) as *mut LeanObject,
        9575030279827742198 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocEval___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__4_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 98, 118, 95, 101, 118, 97, 108, 0],
};
static mut l_Lean_Parser_cbvSimprocEval___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocEval___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocEval___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_cbvSimprocEval: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 95, 67, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99,
        95, 95, 95, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,7509742330559184140 as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value:
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
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value
        ) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value:
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
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value:
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
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value:
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
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value:
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
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value
        ) as *mut LeanObject,
        3961966953292576997 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value:
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
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject,16084902538479694224 as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value) as *mut LeanObject,393173242845875278 as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value) as *mut LeanObject,8609355255726335675 as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value
) as *mut LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value
) as *mut LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 67, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95,
        100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut LeanObject;
static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,3817038020181750064 as *mut LeanObject] };
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    LeanStringObject<18> = LeanStringObject {
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
        99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d__: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
)
    as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<39> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 95, 95, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject;
static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,10086719233862156008 as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject;
static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut LeanObject,17055111195149847261 as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut LeanObject,((( 1022 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d__:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__0_value: LeanStringObject<18> =
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
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_cbvSimprocPattern___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__0_value) as *mut LeanObject,
        5000477209128750040 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__2_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114,
            110, 37, 32, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__5_value: LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPattern___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_cbvSimprocPattern: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117,
            105, 108, 116, 105, 110, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value)
                as *mut LeanObject,
            2235975067317863979 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value: LeanStringObject<30> =
    LeanStringObject {
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
            98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111,
            99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 32, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut LeanObject] };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value) as *mut LeanObject] };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value) as *mut LeanObject] };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_cbvSimprocPatternBuiltin: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value: LeanStringObject<5> =
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
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value: LeanStringObject<15> =
    LeanStringObject {
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
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value)
                as *mut LeanObject,
            9353878392652886871 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_cbvSimprocAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65,
            116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value)
                as *mut LeanObject,
            2685779739350780851 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value: LeanStringObject<20> =
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
            98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111,
            99, 0,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut LeanObject,4498178684837002829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut LeanObject,7625897890118033792 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut LeanObject,8715860392475343861 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut LeanObject,13806531830123099675 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut LeanObject,4585357269266081267 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut LeanObject,8497769072906204829 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut LeanObject,14557702332550915328 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value) as *mut LeanObject;
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value) as *mut LeanObject,9063780239635860524 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value) as *mut LeanObject,11509420844586769999 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value) as *mut LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value) as *mut LeanObject,7983999284776576032 as *mut LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19()
-> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ = l_Lean_Parser_cbvSimprocEval;
    v___x_948_ = l_Lean_Parser_Tactic_simpPost;
    v___x_949_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18;
    v___x_950_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_950_, 0, v___x_949_);
    lean_ctor_set(v___x_950_, 1, v___x_948_);
    lean_ctor_set(v___x_950_, 2, v___x_947_);
    return v___x_950_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20()
-> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19,
    );
    v___x_952_ = l_Lean_Parser_Tactic_simpPre;
    v___x_953_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18;
    v___x_954_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_954_, 0, v___x_953_);
    lean_ctor_set(v___x_954_, 1, v___x_952_);
    lean_ctor_set(v___x_954_, 2, v___x_951_);
    return v___x_954_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21()
-> *mut LeanObject {
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___x_955_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20,
    );
    v___x_956_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5;
    v___x_957_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_957_, 0, v___x_956_);
    lean_ctor_set(v___x_957_, 1, v___x_955_);
    return v___x_957_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22()
-> *mut LeanObject {
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    v___x_958_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_959_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16;
    v___x_960_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_961_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_961_, 0, v___x_960_);
    lean_ctor_set(v___x_961_, 1, v___x_959_);
    lean_ctor_set(v___x_961_, 2, v___x_958_);
    return v___x_961_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26()
-> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25;
    v___x_968_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22,
    );
    v___x_969_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_970_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_970_, 0, v___x_969_);
    lean_ctor_set(v___x_970_, 1, v___x_968_);
    lean_ctor_set(v___x_970_, 2, v___x_967_);
    return v___x_970_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29()
-> *mut LeanObject {
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_974_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28;
    v___x_975_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26,
    );
    v___x_976_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_977_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_977_, 0, v___x_976_);
    lean_ctor_set(v___x_977_, 1, v___x_975_);
    lean_ctor_set(v___x_977_, 2, v___x_974_);
    return v___x_977_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33()
-> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_985_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29,
    );
    v___x_986_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_987_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_987_, 0, v___x_986_);
    lean_ctor_set(v___x_987_, 1, v___x_985_);
    lean_ctor_set(v___x_987_, 2, v___x_984_);
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36()
-> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35;
    v___x_992_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33,
    );
    v___x_993_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_994_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_994_, 0, v___x_993_);
    lean_ctor_set(v___x_994_, 1, v___x_992_);
    lean_ctor_set(v___x_994_, 2, v___x_991_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39()
-> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38;
    v___x_999_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36,
    );
    v___x_1000_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1001_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1001_, 0, v___x_1000_);
    lean_ctor_set(v___x_1001_, 1, v___x_999_);
    lean_ctor_set(v___x_1001_, 2, v___x_998_);
    return v___x_1001_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40()
-> *mut LeanObject {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1002_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1003_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39,
    );
    v___x_1004_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1005_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1005_, 0, v___x_1004_);
    lean_ctor_set(v___x_1005_, 1, v___x_1003_);
    lean_ctor_set(v___x_1005_, 2, v___x_1002_);
    return v___x_1005_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41()
-> *mut LeanObject {
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1006_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40,
    );
    v___x_1007_ = lean_unsigned_to_nat(1022);
    v___x_1008_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
    v___x_1009_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    lean_ctor_set(v___x_1009_, 1, v___x_1007_);
    lean_ctor_set(v___x_1009_, 2, v___x_1006_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41,
    );
    return v___x_1010_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5()
-> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1065_ =
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4;
    v___x_1066_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1067_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1067_, 0, v___x_1066_);
    lean_ctor_set(v___x_1067_, 1, v___x_1065_);
    lean_ctor_set(v___x_1067_, 2, v___x_1064_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6()
-> *mut LeanObject {
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25;
    v___x_1069_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5);
    v___x_1070_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1071_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1071_, 0, v___x_1070_);
    lean_ctor_set(v___x_1071_, 1, v___x_1069_);
    lean_ctor_set(v___x_1071_, 2, v___x_1068_);
    return v___x_1071_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7()
-> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28;
    v___x_1073_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6);
    v___x_1074_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1075_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1075_, 0, v___x_1074_);
    lean_ctor_set(v___x_1075_, 1, v___x_1073_);
    lean_ctor_set(v___x_1075_, 2, v___x_1072_);
    return v___x_1075_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8()
-> *mut LeanObject {
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1077_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7);
    v___x_1078_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1079_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    lean_ctor_set(v___x_1079_, 1, v___x_1077_);
    lean_ctor_set(v___x_1079_, 2, v___x_1076_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9()
-> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35;
    v___x_1081_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8);
    v___x_1082_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1083_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1083_, 0, v___x_1082_);
    lean_ctor_set(v___x_1083_, 1, v___x_1081_);
    lean_ctor_set(v___x_1083_, 2, v___x_1080_);
    return v___x_1083_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10()
-> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38;
    v___x_1085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9);
    v___x_1086_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1087_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1087_, 0, v___x_1086_);
    lean_ctor_set(v___x_1087_, 1, v___x_1085_);
    lean_ctor_set(v___x_1087_, 2, v___x_1084_);
    return v___x_1087_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11()
-> *mut LeanObject {
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    v___x_1088_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1089_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10);
    v___x_1090_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1091_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    lean_ctor_set(v___x_1091_, 1, v___x_1089_);
    lean_ctor_set(v___x_1091_, 2, v___x_1088_);
    return v___x_1091_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12()
-> *mut LeanObject {
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v___x_1092_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11);
    v___x_1093_ = lean_unsigned_to_nat(1022);
    v___x_1094_ =
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
    v___x_1095_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    lean_ctor_set(v___x_1095_, 1, v___x_1093_);
    lean_ctor_set(v___x_1095_, 2, v___x_1092_);
    return v___x_1095_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__()
-> *mut LeanObject {
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v___x_1096_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12);
    return v___x_1096_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5() -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1203_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__4;
    v___x_1204_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1205_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1205_, 0, v___x_1204_);
    lean_ctor_set(v___x_1205_, 1, v___x_1203_);
    lean_ctor_set(v___x_1205_, 2, v___x_1202_);
    return v___x_1205_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6() -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    v___x_1206_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5,
    );
    v___x_1207_ = lean_unsigned_to_nat(1022);
    v___x_1208_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__2;
    v___x_1209_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    lean_ctor_set(v___x_1209_, 1, v___x_1207_);
    lean_ctor_set(v___x_1209_, 2, v___x_1206_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr() -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v___x_1210_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once),
        _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6,
    );
    return v___x_1210_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4() -> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1222_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3;
    v___x_1223_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1224_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_1224_, 0, v___x_1223_);
    lean_ctor_set(v___x_1224_, 1, v___x_1222_);
    lean_ctor_set(v___x_1224_, 2, v___x_1221_);
    return v___x_1224_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5() -> *mut LeanObject {
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    v___x_1225_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4,
    );
    v___x_1226_ = lean_unsigned_to_nat(1022);
    v___x_1227_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1;
    v___x_1228_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_1228_, 0, v___x_1227_);
    lean_ctor_set(v___x_1228_, 1, v___x_1226_);
    lean_ctor_set(v___x_1228_, 2, v___x_1225_);
    return v___x_1228_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr() -> *mut LeanObject {
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_1229_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5,
    );
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28()
-> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_Array_mkArray0(lean_box(0));
    return v___x_1280_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u8 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1291_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1292_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1374_ =
                    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_1288_);
                v___x_1375_ = l_Lean_Syntax_isOfKind(v_x_1288_, v___x_1374_);
                if v___x_1375_ == 0 {
                    lean_dec(v_x_1288_);
                    v___x_1376_ = lean_box(1);
                    v___x_1377_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                    lean_ctor_set(v___x_1377_, 1, v_a_1290_);
                    return v___x_1377_;
                } else {
                    v___x_1378_ = lean_unsigned_to_nat(0);
                    v___x_1379_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1378_);
                    v___x_1380_ = l_Lean_Syntax_isNone(v___x_1379_);
                    if v___x_1380_ == 0 {
                        v___x_1381_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_1379_);
                        v___x_1382_ = l_Lean_Syntax_matchesNull(v___x_1379_, v___x_1381_);
                        if v___x_1382_ == 0 {
                            lean_dec(v___x_1379_);
                            lean_dec(v_x_1288_);
                            v___x_1383_ = lean_box(1);
                            v___x_1384_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1384_, 0, v___x_1383_);
                            lean_ctor_set(v___x_1384_, 1, v_a_1290_);
                            return v___x_1384_;
                        } else {
                            v_doc_x3f_1385_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1378_);
                            lean_dec(v___x_1379_);
                            v___x_1386_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            lean_inc(v_doc_x3f_1385_);
                            v___x_1387_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1385_, v___x_1386_);
                            if v___x_1387_ == 0 {
                                lean_dec(v_doc_x3f_1385_);
                                lean_dec(v_x_1288_);
                                v___x_1388_ = lean_box(1);
                                v___x_1389_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1389_, 0, v___x_1388_);
                                lean_ctor_set(v___x_1389_, 1, v_a_1290_);
                                return v___x_1389_;
                            } else {
                                v___x_1390_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1390_, 0, v_doc_x3f_1385_);
                                v_doc_x3f_1349_ = v___x_1390_;
                                v___y_1350_ = v_a_1289_;
                                v___y_1351_ = v_a_1290_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1379_);
                        v___x_1391_ = lean_box(0);
                        v_doc_x3f_1349_ = v___x_1391_;
                        v___y_1350_ = v_a_1289_;
                        v___y_1351_ = v_a_1290_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_1300_, 2);
                v___x_1306_ = l_Array_append___redArg(v___y_1300_, v___y_1305_);
                lean_dec_ref(v___y_1305_);
                lean_inc_n(v___y_1296_, 5);
                lean_inc_n(v___y_1297_, 20);
                v___x_1307_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1307_, 0, v___y_1297_);
                lean_ctor_set(v___x_1307_, 1, v___y_1296_);
                lean_ctor_set(v___x_1307_, 2, v___x_1306_);
                v___x_1308_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1308_, 0, v___y_1297_);
                lean_ctor_set(v___x_1308_, 1, v___y_1296_);
                lean_ctor_set(v___x_1308_, 2, v___y_1300_);
                v___x_1309_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                lean_inc_ref_n(v___y_1304_, 5);
                v___x_1310_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1309_);
                v___x_1311_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1311_, 0, v___y_1297_);
                lean_ctor_set(v___x_1311_, 1, v___x_1309_);
                v___x_1312_ = l_Lean_Syntax_node1(v___y_1297_, v___x_1310_, v___x_1311_);
                v___x_1313_ = l_Lean_Syntax_node1(v___y_1297_, v___y_1296_, v___x_1312_);
                lean_inc_ref_n(v___x_1308_, 10);
                lean_inc(v___y_1295_);
                v___x_1314_ = l_Lean_Syntax_node7(
                    v___y_1297_,
                    v___y_1295_,
                    v___x_1307_,
                    v___x_1308_,
                    v___x_1308_,
                    v___x_1308_,
                    v___x_1313_,
                    v___x_1308_,
                    v___x_1308_,
                );
                v___x_1315_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                v___x_1316_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1315_);
                v___x_1317_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_1318_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1318_, 0, v___y_1297_);
                lean_ctor_set(v___x_1318_, 1, v___x_1317_);
                v___x_1319_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_1320_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1319_);
                lean_inc(v___y_1299_);
                v___x_1321_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1320_, v___y_1299_, v___x_1308_);
                v___x_1322_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_1323_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1322_);
                v___x_1324_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_1325_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_1326_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1326_, 0, v___y_1297_);
                lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                lean_inc(v___y_1294_);
                v___x_1327_ = lean_mk_syntax_ident(v___y_1294_);
                v___x_1328_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1324_, v___x_1326_, v___x_1327_);
                v___x_1329_ = l_Lean_Syntax_node1(v___y_1297_, v___y_1296_, v___x_1328_);
                v___x_1330_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1323_, v___x_1308_, v___x_1329_);
                v___x_1331_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_1332_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1331_);
                v___x_1333_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1334_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1334_, 0, v___y_1297_);
                lean_ctor_set(v___x_1334_, 1, v___x_1333_);
                v___x_1335_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_1336_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1335_, v___x_1308_, v___x_1308_);
                v___x_1337_ = l_Lean_Syntax_node4(
                    v___y_1297_,
                    v___x_1332_,
                    v___x_1334_,
                    v___y_1302_,
                    v___x_1336_,
                    v___x_1308_,
                );
                v___x_1338_ = l_Lean_Syntax_node5(
                    v___y_1297_,
                    v___x_1316_,
                    v___x_1318_,
                    v___x_1321_,
                    v___x_1330_,
                    v___x_1337_,
                    v___x_1308_,
                );
                lean_inc(v___y_1303_);
                v___x_1339_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___y_1303_, v___x_1314_, v___x_1338_);
                v___x_1340_ = l_Lean_Parser_cbvSimprocPattern___closed__1;
                v___x_1341_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_1342_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1342_, 0, v___y_1297_);
                lean_ctor_set(v___x_1342_, 1, v___x_1341_);
                v___x_1343_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_1344_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1344_, 0, v___y_1297_);
                lean_ctor_set(v___x_1344_, 1, v___x_1343_);
                v___x_1345_ = l_Lean_Syntax_node4(
                    v___y_1297_,
                    v___x_1340_,
                    v___x_1342_,
                    v___y_1298_,
                    v___x_1344_,
                    v___y_1299_,
                );
                v___x_1346_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___y_1296_, v___x_1339_, v___x_1345_);
                v___x_1347_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1347_, 0, v___x_1346_);
                lean_ctor_set(v___x_1347_, 1, v___y_1301_);
                return v___x_1347_;
            }
            2 => {
                v___x_1352_ = lean_unsigned_to_nat(2);
                v___x_1353_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1352_);
                v___x_1354_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                lean_inc(v___x_1353_);
                v___x_1355_ = l_Lean_Syntax_isOfKind(v___x_1353_, v___x_1354_);
                if v___x_1355_ == 0 {
                    lean_dec(v___x_1353_);
                    lean_dec(v_doc_x3f_1349_);
                    lean_dec(v_x_1288_);
                    v___x_1356_ = lean_box(1);
                    v___x_1357_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                    lean_ctor_set(v___x_1357_, 1, v___y_1351_);
                    return v___x_1357_;
                } else {
                    v_ref_1358_ = lean_ctor_get(v___y_1350_, 5);
                    v___x_1359_ = lean_unsigned_to_nat(4);
                    v___x_1360_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1359_);
                    v___x_1361_ = lean_unsigned_to_nat(7);
                    v___x_1362_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1361_);
                    lean_dec(v_x_1288_);
                    v_simprocType_1363_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20;
                    v___x_1364_ = 0;
                    v___x_1365_ = l_Lean_SourceInfo_fromRef(v_ref_1358_, v___x_1364_);
                    v___x_1366_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1367_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23;
                    v___x_1368_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25;
                    v___x_1369_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27;
                    v___x_1370_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if lean_obj_tag(v_doc_x3f_1349_) == 1 {
                        v_val_1371_ = lean_ctor_get(v_doc_x3f_1349_, 0);
                        lean_inc(v_val_1371_);
                        lean_dec_ref_known(v_doc_x3f_1349_, 1);
                        v___x_1372_ = l_Array_mkArray1___redArg(v_val_1371_);
                        v___y_1294_ = v_simprocType_1363_;
                        v___y_1295_ = v___x_1369_;
                        v___y_1296_ = v___x_1366_;
                        v___y_1297_ = v___x_1365_;
                        v___y_1298_ = v___x_1360_;
                        v___y_1299_ = v___x_1353_;
                        v___y_1300_ = v___x_1370_;
                        v___y_1301_ = v___y_1351_;
                        v___y_1302_ = v___x_1362_;
                        v___y_1303_ = v___x_1368_;
                        v___y_1304_ = v___x_1367_;
                        v___y_1305_ = v___x_1372_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_doc_x3f_1349_);
                        v___x_1373_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1294_ = v_simprocType_1363_;
                        v___y_1295_ = v___x_1369_;
                        v___y_1296_ = v___x_1366_;
                        v___y_1297_ = v___x_1365_;
                        v___y_1298_ = v___x_1360_;
                        v___y_1299_ = v___x_1353_;
                        v___y_1300_ = v___x_1370_;
                        v___y_1301_ = v___y_1351_;
                        v___y_1302_ = v___x_1362_;
                        v___y_1303_ = v___x_1368_;
                        v___y_1304_ = v___x_1367_;
                        v___y_1305_ = v___x_1373_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1395_: *mut LeanObject = core::ptr::null_mut();
    v_res_1395_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_1392_, v_a_1393_, v_a_1394_);
    lean_dec_ref(v_a_1393_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simprocType_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1401_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1478_ = l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_1397_);
                v___x_1479_ = l_Lean_Syntax_isOfKind(v_x_1397_, v___x_1478_);
                if v___x_1479_ == 0 {
                    lean_dec(v_x_1397_);
                    v___x_1480_ = lean_box(1);
                    v___x_1481_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                    lean_ctor_set(v___x_1481_, 1, v_a_1399_);
                    return v___x_1481_;
                } else {
                    v___x_1482_ = lean_unsigned_to_nat(0);
                    v___x_1483_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1482_);
                    v___x_1484_ = l_Lean_Syntax_isNone(v___x_1483_);
                    if v___x_1484_ == 0 {
                        v___x_1485_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_1483_);
                        v___x_1486_ = l_Lean_Syntax_matchesNull(v___x_1483_, v___x_1485_);
                        if v___x_1486_ == 0 {
                            lean_dec(v___x_1483_);
                            lean_dec(v_x_1397_);
                            v___x_1487_ = lean_box(1);
                            v___x_1488_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                            lean_ctor_set(v___x_1488_, 1, v_a_1399_);
                            return v___x_1488_;
                        } else {
                            v_doc_x3f_1489_ = l_Lean_Syntax_getArg(v___x_1483_, v___x_1482_);
                            lean_dec(v___x_1483_);
                            v___x_1490_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            lean_inc(v_doc_x3f_1489_);
                            v___x_1491_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1489_, v___x_1490_);
                            if v___x_1491_ == 0 {
                                lean_dec(v_doc_x3f_1489_);
                                lean_dec(v_x_1397_);
                                v___x_1492_ = lean_box(1);
                                v___x_1493_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1493_, 0, v___x_1492_);
                                lean_ctor_set(v___x_1493_, 1, v_a_1399_);
                                return v___x_1493_;
                            } else {
                                v___x_1494_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1494_, 0, v_doc_x3f_1489_);
                                v_doc_x3f_1453_ = v___x_1494_;
                                v___y_1454_ = v_a_1398_;
                                v___y_1455_ = v_a_1399_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1483_);
                        v___x_1495_ = lean_box(0);
                        v_doc_x3f_1453_ = v___x_1495_;
                        v___y_1454_ = v_a_1398_;
                        v___y_1455_ = v_a_1399_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref_n(v___y_1405_, 2);
                v___x_1415_ = l_Array_append___redArg(v___y_1405_, v___y_1414_);
                lean_dec_ref(v___y_1414_);
                lean_inc_n(v___y_1413_, 4);
                lean_inc_n(v___y_1404_, 17);
                v___x_1416_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1416_, 0, v___y_1404_);
                lean_ctor_set(v___x_1416_, 1, v___y_1413_);
                lean_ctor_set(v___x_1416_, 2, v___x_1415_);
                v___x_1417_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1417_, 0, v___y_1404_);
                lean_ctor_set(v___x_1417_, 1, v___y_1413_);
                lean_ctor_set(v___x_1417_, 2, v___y_1405_);
                lean_inc_ref_n(v___x_1417_, 11);
                lean_inc(v___y_1412_);
                v___x_1418_ = l_Lean_Syntax_node7(
                    v___y_1404_,
                    v___y_1412_,
                    v___x_1416_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                );
                v___x_1419_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                lean_inc_ref_n(v___y_1406_, 4);
                v___x_1420_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1419_);
                v___x_1421_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_1422_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1422_, 0, v___y_1404_);
                lean_ctor_set(v___x_1422_, 1, v___x_1421_);
                v___x_1423_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_1424_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1423_);
                lean_inc(v___y_1411_);
                v___x_1425_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1424_, v___y_1411_, v___x_1417_);
                v___x_1426_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_1427_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1426_);
                v___x_1428_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_1429_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_1430_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1430_, 0, v___y_1404_);
                lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                lean_inc(v___y_1403_);
                v___x_1431_ = lean_mk_syntax_ident(v___y_1403_);
                v___x_1432_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1428_, v___x_1430_, v___x_1431_);
                v___x_1433_ = l_Lean_Syntax_node1(v___y_1404_, v___y_1413_, v___x_1432_);
                v___x_1434_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1427_, v___x_1417_, v___x_1433_);
                v___x_1435_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_1436_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1435_);
                v___x_1437_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1438_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1438_, 0, v___y_1404_);
                lean_ctor_set(v___x_1438_, 1, v___x_1437_);
                v___x_1439_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_1440_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1439_, v___x_1417_, v___x_1417_);
                v___x_1441_ = l_Lean_Syntax_node4(
                    v___y_1404_,
                    v___x_1436_,
                    v___x_1438_,
                    v___y_1408_,
                    v___x_1440_,
                    v___x_1417_,
                );
                v___x_1442_ = l_Lean_Syntax_node5(
                    v___y_1404_,
                    v___x_1420_,
                    v___x_1422_,
                    v___x_1425_,
                    v___x_1434_,
                    v___x_1441_,
                    v___x_1417_,
                );
                lean_inc(v___y_1410_);
                v___x_1443_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___y_1410_, v___x_1418_, v___x_1442_);
                v___x_1444_ = l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1;
                v___x_1445_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_1446_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1446_, 0, v___y_1404_);
                lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_1448_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1448_, 0, v___y_1404_);
                lean_ctor_set(v___x_1448_, 1, v___x_1447_);
                v___x_1449_ = l_Lean_Syntax_node4(
                    v___y_1404_,
                    v___x_1444_,
                    v___x_1446_,
                    v___y_1409_,
                    v___x_1448_,
                    v___y_1411_,
                );
                v___x_1450_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___y_1413_, v___x_1443_, v___x_1449_);
                v___x_1451_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                lean_ctor_set(v___x_1451_, 1, v___y_1407_);
                return v___x_1451_;
            }
            2 => {
                v___x_1456_ = lean_unsigned_to_nat(2);
                v___x_1457_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1456_);
                v___x_1458_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                lean_inc(v___x_1457_);
                v___x_1459_ = l_Lean_Syntax_isOfKind(v___x_1457_, v___x_1458_);
                if v___x_1459_ == 0 {
                    lean_dec(v___x_1457_);
                    lean_dec(v_doc_x3f_1453_);
                    lean_dec(v_x_1397_);
                    v___x_1460_ = lean_box(1);
                    v___x_1461_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1461_, 0, v___x_1460_);
                    lean_ctor_set(v___x_1461_, 1, v___y_1455_);
                    return v___x_1461_;
                } else {
                    v_ref_1462_ = lean_ctor_get(v___y_1454_, 5);
                    v___x_1463_ = lean_unsigned_to_nat(4);
                    v___x_1464_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1463_);
                    v___x_1465_ = lean_unsigned_to_nat(7);
                    v___x_1466_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1465_);
                    lean_dec(v_x_1397_);
                    v_simprocType_1467_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20;
                    v___x_1468_ = 0;
                    v___x_1469_ = l_Lean_SourceInfo_fromRef(v_ref_1462_, v___x_1468_);
                    v___x_1470_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1471_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23;
                    v___x_1472_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25;
                    v___x_1473_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27;
                    v___x_1474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if lean_obj_tag(v_doc_x3f_1453_) == 1 {
                        v_val_1475_ = lean_ctor_get(v_doc_x3f_1453_, 0);
                        lean_inc(v_val_1475_);
                        lean_dec_ref_known(v_doc_x3f_1453_, 1);
                        v___x_1476_ = l_Array_mkArray1___redArg(v_val_1475_);
                        v___y_1403_ = v_simprocType_1467_;
                        v___y_1404_ = v___x_1469_;
                        v___y_1405_ = v___x_1474_;
                        v___y_1406_ = v___x_1471_;
                        v___y_1407_ = v___y_1455_;
                        v___y_1408_ = v___x_1466_;
                        v___y_1409_ = v___x_1464_;
                        v___y_1410_ = v___x_1472_;
                        v___y_1411_ = v___x_1457_;
                        v___y_1412_ = v___x_1473_;
                        v___y_1413_ = v___x_1470_;
                        v___y_1414_ = v___x_1476_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_doc_x3f_1453_);
                        v___x_1477_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1403_ = v_simprocType_1467_;
                        v___y_1404_ = v___x_1469_;
                        v___y_1405_ = v___x_1474_;
                        v___y_1406_ = v___x_1471_;
                        v___y_1407_ = v___y_1455_;
                        v___y_1408_ = v___x_1466_;
                        v___y_1409_ = v___x_1464_;
                        v___y_1410_ = v___x_1472_;
                        v___y_1411_ = v___x_1457_;
                        v___y_1412_ = v___x_1473_;
                        v___y_1413_ = v___x_1470_;
                        v___y_1414_ = v___x_1477_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1499_: *mut LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_1496_, v_a_1497_, v_a_1498_);
    lean_dec_ref(v_a_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(
    mut v_x_1516_: *mut LeanObject,
    mut v_a_1517_: *mut LeanObject,
    mut v_a_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1545_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1546_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1547_ =
                    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_1516_);
                v___x_1548_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1547_);
                if v___x_1548_ == 0 {
                    lean_dec(v_x_1516_);
                    v___x_1549_ = lean_box(1);
                    v___x_1550_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1550_, 0, v___x_1549_);
                    lean_ctor_set(v___x_1550_, 1, v_a_1518_);
                    return v___x_1550_;
                } else {
                    v___x_1551_ = lean_unsigned_to_nat(0);
                    v___x_1634_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1551_);
                    v___x_1635_ = l_Lean_Syntax_isNone(v___x_1634_);
                    if v___x_1635_ == 0 {
                        v___x_1636_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_1634_);
                        v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1634_, v___x_1636_);
                        if v___x_1637_ == 0 {
                            lean_dec(v___x_1634_);
                            lean_dec(v_x_1516_);
                            v___x_1638_ = lean_box(1);
                            v___x_1639_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1639_, 0, v___x_1638_);
                            lean_ctor_set(v___x_1639_, 1, v_a_1518_);
                            return v___x_1639_;
                        } else {
                            v_doc_x3f_1640_ = l_Lean_Syntax_getArg(v___x_1634_, v___x_1551_);
                            lean_dec(v___x_1634_);
                            v___x_1641_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            lean_inc(v_doc_x3f_1640_);
                            v___x_1642_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1640_, v___x_1641_);
                            if v___x_1642_ == 0 {
                                lean_dec(v_doc_x3f_1640_);
                                lean_dec(v_x_1516_);
                                v___x_1643_ = lean_box(1);
                                v___x_1644_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1644_, 0, v___x_1643_);
                                lean_ctor_set(v___x_1644_, 1, v_a_1518_);
                                return v___x_1644_;
                            } else {
                                v___x_1645_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1645_, 0, v_doc_x3f_1640_);
                                v_doc_x3f_1616_ = v___x_1645_;
                                v___y_1617_ = v_a_1517_;
                                v___y_1618_ = v_a_1518_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1634_);
                        v___x_1646_ = lean_box(0);
                        v_doc_x3f_1616_ = v___x_1646_;
                        v___y_1617_ = v_a_1517_;
                        v___y_1618_ = v_a_1518_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_1524_);
                v___x_1534_ = l_Array_append___redArg(v___y_1524_, v___y_1533_);
                lean_dec_ref(v___y_1533_);
                lean_inc_n(v___y_1531_, 4);
                lean_inc_n(v___y_1522_, 7);
                v___x_1535_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1535_, 0, v___y_1522_);
                lean_ctor_set(v___x_1535_, 1, v___y_1531_);
                lean_ctor_set(v___x_1535_, 2, v___x_1534_);
                lean_inc(v___y_1529_);
                v___x_1536_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1529_, v___y_1525_, v___x_1535_);
                v___x_1537_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1521_, v___y_1530_, v___x_1536_);
                v___x_1538_ = l_Lean_Syntax_node1(v___y_1522_, v___y_1531_, v___x_1537_);
                v___x_1539_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1540_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1540_, 0, v___y_1522_);
                lean_ctor_set(v___x_1540_, 1, v___x_1539_);
                v___x_1541_ = l_Lean_Syntax_node1(v___y_1522_, v___y_1531_, v___y_1523_);
                lean_inc(v___y_1526_);
                v___x_1542_ = l_Lean_Syntax_node5(
                    v___y_1522_,
                    v___y_1526_,
                    v___y_1532_,
                    v___y_1527_,
                    v___x_1538_,
                    v___x_1540_,
                    v___x_1541_,
                );
                v___x_1543_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1531_, v___y_1520_, v___x_1542_);
                v___x_1544_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1544_, 0, v___x_1543_);
                lean_ctor_set(v___x_1544_, 1, v___y_1528_);
                return v___x_1544_;
            }
            2 => {
                lean_inc_ref(v___y_1561_);
                v___x_1565_ = l_Array_append___redArg(v___y_1561_, v___y_1564_);
                lean_dec_ref(v___y_1564_);
                lean_inc(v___y_1559_);
                lean_inc_n(v___y_1556_, 9);
                v___x_1566_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1566_, 0, v___y_1556_);
                lean_ctor_set(v___x_1566_, 1, v___y_1559_);
                lean_ctor_set(v___x_1566_, 2, v___x_1565_);
                v___x_1567_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1;
                v___x_1568_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1568_, 0, v___y_1556_);
                lean_ctor_set(v___x_1568_, 1, v___x_1567_);
                v___x_1569_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2;
                v___x_1570_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1570_, 0, v___y_1556_);
                lean_ctor_set(v___x_1570_, 1, v___x_1569_);
                v___x_1571_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34;
                v___x_1572_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1572_, 0, v___y_1556_);
                lean_ctor_set(v___x_1572_, 1, v___x_1571_);
                v___x_1573_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1574_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1574_, 0, v___y_1556_);
                lean_ctor_set(v___x_1574_, 1, v___x_1573_);
                lean_inc(v___y_1558_);
                lean_inc(v___y_1563_);
                v___x_1575_ = l_Lean_Syntax_node8(
                    v___y_1556_,
                    v___y_1563_,
                    v___x_1566_,
                    v___x_1568_,
                    v___y_1558_,
                    v___x_1570_,
                    v___y_1560_,
                    v___x_1572_,
                    v___x_1574_,
                    v___y_1553_,
                );
                v___x_1576_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3;
                v___x_1577_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4;
                v___x_1578_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1578_, 0, v___y_1556_);
                lean_ctor_set(v___x_1578_, 1, v___x_1576_);
                v___x_1579_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5;
                v___x_1580_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1580_, 0, v___y_1556_);
                lean_ctor_set(v___x_1580_, 1, v___x_1579_);
                v___x_1581_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6;
                lean_inc_ref(v___y_1562_);
                v___x_1582_ =
                    l_Lean_Name_mkStr4(v___x_1545_, v___x_1546_, v___y_1562_, v___x_1581_);
                v___x_1583_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__2;
                v___x_1584_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__3;
                v___x_1585_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1585_, 0, v___y_1556_);
                lean_ctor_set(v___x_1585_, 1, v___x_1584_);
                if lean_obj_tag(v___y_1557_) == 1 {
                    v_val_1586_ = lean_ctor_get(v___y_1557_, 0);
                    lean_inc(v_val_1586_);
                    lean_dec_ref_known(v___y_1557_, 1);
                    v___x_1587_ = l_Array_mkArray1___redArg(v_val_1586_);
                    v___y_1520_ = v___x_1575_;
                    v___y_1521_ = v___x_1582_;
                    v___y_1522_ = v___y_1556_;
                    v___y_1523_ = v___y_1558_;
                    v___y_1524_ = v___y_1561_;
                    v___y_1525_ = v___x_1585_;
                    v___y_1526_ = v___x_1577_;
                    v___y_1527_ = v___x_1580_;
                    v___y_1528_ = v___y_1554_;
                    v___y_1529_ = v___x_1583_;
                    v___y_1530_ = v___y_1555_;
                    v___y_1531_ = v___y_1559_;
                    v___y_1532_ = v___x_1578_;
                    v___y_1533_ = v___x_1587_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1557_);
                    v___x_1588_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                    v___y_1520_ = v___x_1575_;
                    v___y_1521_ = v___x_1582_;
                    v___y_1522_ = v___y_1556_;
                    v___y_1523_ = v___y_1558_;
                    v___y_1524_ = v___y_1561_;
                    v___y_1525_ = v___x_1585_;
                    v___y_1526_ = v___x_1577_;
                    v___y_1527_ = v___x_1580_;
                    v___y_1528_ = v___y_1554_;
                    v___y_1529_ = v___x_1583_;
                    v___y_1530_ = v___y_1555_;
                    v___y_1531_ = v___y_1559_;
                    v___y_1532_ = v___x_1578_;
                    v___y_1533_ = v___x_1588_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1595_ = lean_unsigned_to_nat(4);
                v___x_1596_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1595_);
                v___x_1597_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                lean_inc(v___x_1596_);
                v___x_1598_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1597_);
                if v___x_1598_ == 0 {
                    lean_dec(v___x_1596_);
                    lean_dec(v_phase_x3f_1592_);
                    lean_dec(v___y_1591_);
                    lean_dec(v___y_1590_);
                    lean_dec(v_x_1516_);
                    v___x_1599_ = lean_box(1);
                    v___x_1600_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1600_, 0, v___x_1599_);
                    lean_ctor_set(v___x_1600_, 1, v___y_1594_);
                    return v___x_1600_;
                } else {
                    v_ref_1601_ = lean_ctor_get(v___y_1593_, 5);
                    v___x_1602_ = lean_unsigned_to_nat(6);
                    v___x_1603_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1602_);
                    v___x_1604_ = lean_unsigned_to_nat(9);
                    v___x_1605_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1604_);
                    lean_dec(v_x_1516_);
                    v___x_1606_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                    v___x_1607_ = 0;
                    v___x_1608_ = l_Lean_SourceInfo_fromRef(v_ref_1601_, v___x_1607_);
                    v___x_1609_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1610_ = l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_1611_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if lean_obj_tag(v___y_1591_) == 1 {
                        v_val_1612_ = lean_ctor_get(v___y_1591_, 0);
                        lean_inc(v_val_1612_);
                        lean_dec_ref_known(v___y_1591_, 1);
                        v___x_1613_ = l_Array_mkArray1___redArg(v_val_1612_);
                        v___y_1553_ = v___x_1605_;
                        v___y_1554_ = v___y_1594_;
                        v___y_1555_ = v___y_1590_;
                        v___y_1556_ = v___x_1608_;
                        v___y_1557_ = v_phase_x3f_1592_;
                        v___y_1558_ = v___x_1596_;
                        v___y_1559_ = v___x_1609_;
                        v___y_1560_ = v___x_1603_;
                        v___y_1561_ = v___x_1611_;
                        v___y_1562_ = v___x_1606_;
                        v___y_1563_ = v___x_1610_;
                        v___y_1564_ = v___x_1613_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_1591_);
                        v___x_1614_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1553_ = v___x_1605_;
                        v___y_1554_ = v___y_1594_;
                        v___y_1555_ = v___y_1590_;
                        v___y_1556_ = v___x_1608_;
                        v___y_1557_ = v_phase_x3f_1592_;
                        v___y_1558_ = v___x_1596_;
                        v___y_1559_ = v___x_1609_;
                        v___y_1560_ = v___x_1603_;
                        v___y_1561_ = v___x_1611_;
                        v___y_1562_ = v___x_1606_;
                        v___y_1563_ = v___x_1610_;
                        v___y_1564_ = v___x_1614_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1619_ = lean_unsigned_to_nat(1);
                v___x_1620_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1619_);
                v___x_1621_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7;
                lean_inc(v___x_1620_);
                v___x_1622_ = l_Lean_Syntax_isOfKind(v___x_1620_, v___x_1621_);
                if v___x_1622_ == 0 {
                    lean_dec(v___x_1620_);
                    lean_dec(v_doc_x3f_1616_);
                    lean_dec(v_x_1516_);
                    v___x_1623_ = lean_box(1);
                    v___x_1624_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1624_, 0, v___x_1623_);
                    lean_ctor_set(v___x_1624_, 1, v___y_1618_);
                    return v___x_1624_;
                } else {
                    v___x_1625_ = lean_unsigned_to_nat(3);
                    v___x_1626_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1625_);
                    v___x_1627_ = l_Lean_Syntax_isNone(v___x_1626_);
                    if v___x_1627_ == 0 {
                        lean_inc(v___x_1626_);
                        v___x_1628_ = l_Lean_Syntax_matchesNull(v___x_1626_, v___x_1619_);
                        if v___x_1628_ == 0 {
                            lean_dec(v___x_1626_);
                            lean_dec(v___x_1620_);
                            lean_dec(v_doc_x3f_1616_);
                            lean_dec(v_x_1516_);
                            v___x_1629_ = lean_box(1);
                            v___x_1630_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1630_, 0, v___x_1629_);
                            lean_ctor_set(v___x_1630_, 1, v___y_1618_);
                            return v___x_1630_;
                        } else {
                            v_phase_x3f_1631_ = l_Lean_Syntax_getArg(v___x_1626_, v___x_1551_);
                            lean_dec(v___x_1626_);
                            v___x_1632_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1632_, 0, v_phase_x3f_1631_);
                            v___y_1590_ = v___x_1620_;
                            v___y_1591_ = v_doc_x3f_1616_;
                            v_phase_x3f_1592_ = v___x_1632_;
                            v___y_1593_ = v___y_1617_;
                            v___y_1594_ = v___y_1618_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1626_);
                        v___x_1633_ = lean_box(0);
                        v___y_1590_ = v___x_1620_;
                        v___y_1591_ = v_doc_x3f_1616_;
                        v_phase_x3f_1592_ = v___x_1633_;
                        v___y_1593_ = v___y_1617_;
                        v___y_1594_ = v___y_1618_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(
    mut v_x_1647_: *mut LeanObject,
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1650_: *mut LeanObject = core::ptr::null_mut();
    v_res_1650_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(v_x_1647_, v_a_1648_, v_a_1649_);
    lean_dec_ref(v_a_1648_);
    return v_res_1650_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(
    mut v_x_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1681_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1682_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1683_ = l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
                lean_inc(v_x_1652_);
                v___x_1684_ = l_Lean_Syntax_isOfKind(v_x_1652_, v___x_1683_);
                if v___x_1684_ == 0 {
                    lean_dec(v_x_1652_);
                    v___x_1685_ = lean_box(1);
                    v___x_1686_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1686_, 0, v___x_1685_);
                    lean_ctor_set(v___x_1686_, 1, v_a_1654_);
                    return v___x_1686_;
                } else {
                    v___x_1687_ = lean_unsigned_to_nat(0);
                    v___x_1770_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1687_);
                    v___x_1771_ = l_Lean_Syntax_isNone(v___x_1770_);
                    if v___x_1771_ == 0 {
                        v___x_1772_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_1770_);
                        v___x_1773_ = l_Lean_Syntax_matchesNull(v___x_1770_, v___x_1772_);
                        if v___x_1773_ == 0 {
                            lean_dec(v___x_1770_);
                            lean_dec(v_x_1652_);
                            v___x_1774_ = lean_box(1);
                            v___x_1775_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                            lean_ctor_set(v___x_1775_, 1, v_a_1654_);
                            return v___x_1775_;
                        } else {
                            v_doc_x3f_1776_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1687_);
                            lean_dec(v___x_1770_);
                            v___x_1777_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            lean_inc(v_doc_x3f_1776_);
                            v___x_1778_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1776_, v___x_1777_);
                            if v___x_1778_ == 0 {
                                lean_dec(v_doc_x3f_1776_);
                                lean_dec(v_x_1652_);
                                v___x_1779_ = lean_box(1);
                                v___x_1780_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1780_, 0, v___x_1779_);
                                lean_ctor_set(v___x_1780_, 1, v_a_1654_);
                                return v___x_1780_;
                            } else {
                                v___x_1781_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1781_, 0, v_doc_x3f_1776_);
                                v_doc_x3f_1752_ = v___x_1781_;
                                v___y_1753_ = v_a_1653_;
                                v___y_1754_ = v_a_1654_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1770_);
                        v___x_1782_ = lean_box(0);
                        v_doc_x3f_1752_ = v___x_1782_;
                        v___y_1753_ = v_a_1653_;
                        v___y_1754_ = v_a_1654_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_1663_);
                v___x_1670_ = l_Array_append___redArg(v___y_1663_, v___y_1669_);
                lean_dec_ref(v___y_1669_);
                lean_inc_n(v___y_1664_, 4);
                lean_inc_n(v___y_1661_, 7);
                v___x_1671_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1671_, 0, v___y_1661_);
                lean_ctor_set(v___x_1671_, 1, v___y_1664_);
                lean_ctor_set(v___x_1671_, 2, v___x_1670_);
                lean_inc(v___y_1656_);
                v___x_1672_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1656_, v___y_1660_, v___x_1671_);
                v___x_1673_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1658_, v___y_1662_, v___x_1672_);
                v___x_1674_ = l_Lean_Syntax_node1(v___y_1661_, v___y_1664_, v___x_1673_);
                v___x_1675_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1676_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1676_, 0, v___y_1661_);
                lean_ctor_set(v___x_1676_, 1, v___x_1675_);
                v___x_1677_ = l_Lean_Syntax_node1(v___y_1661_, v___y_1664_, v___y_1665_);
                lean_inc(v___y_1667_);
                v___x_1678_ = l_Lean_Syntax_node5(
                    v___y_1661_,
                    v___y_1667_,
                    v___y_1668_,
                    v___y_1659_,
                    v___x_1674_,
                    v___x_1676_,
                    v___x_1677_,
                );
                v___x_1679_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1664_, v___y_1666_, v___x_1678_);
                v___x_1680_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1680_, 0, v___x_1679_);
                lean_ctor_set(v___x_1680_, 1, v___y_1657_);
                return v___x_1680_;
            }
            2 => {
                lean_inc_ref(v___y_1689_);
                v___x_1701_ = l_Array_append___redArg(v___y_1689_, v___y_1700_);
                lean_dec_ref(v___y_1700_);
                lean_inc(v___y_1692_);
                lean_inc_n(v___y_1694_, 9);
                v___x_1702_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1702_, 0, v___y_1694_);
                lean_ctor_set(v___x_1702_, 1, v___y_1692_);
                lean_ctor_set(v___x_1702_, 2, v___x_1701_);
                v___x_1703_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1704_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v___y_1694_);
                lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                v___x_1705_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2;
                v___x_1706_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1706_, 0, v___y_1694_);
                lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                v___x_1707_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34;
                v___x_1708_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1708_, 0, v___y_1694_);
                lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                v___x_1709_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1710_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1710_, 0, v___y_1694_);
                lean_ctor_set(v___x_1710_, 1, v___x_1709_);
                lean_inc(v___y_1695_);
                lean_inc(v___y_1693_);
                v___x_1711_ = l_Lean_Syntax_node8(
                    v___y_1694_,
                    v___y_1693_,
                    v___x_1702_,
                    v___x_1704_,
                    v___y_1695_,
                    v___x_1706_,
                    v___y_1696_,
                    v___x_1708_,
                    v___x_1710_,
                    v___y_1691_,
                );
                v___x_1712_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3;
                v___x_1713_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4;
                v___x_1714_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1714_, 0, v___y_1694_);
                lean_ctor_set(v___x_1714_, 1, v___x_1712_);
                v___x_1715_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5;
                v___x_1716_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1716_, 0, v___y_1694_);
                lean_ctor_set(v___x_1716_, 1, v___x_1715_);
                v___x_1717_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6;
                lean_inc_ref(v___y_1699_);
                v___x_1718_ =
                    l_Lean_Name_mkStr4(v___x_1681_, v___x_1682_, v___y_1699_, v___x_1717_);
                v___x_1719_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1;
                v___x_1720_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2;
                v___x_1721_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1721_, 0, v___y_1694_);
                lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                if lean_obj_tag(v___y_1697_) == 1 {
                    v_val_1722_ = lean_ctor_get(v___y_1697_, 0);
                    lean_inc(v_val_1722_);
                    lean_dec_ref_known(v___y_1697_, 1);
                    v___x_1723_ = l_Array_mkArray1___redArg(v_val_1722_);
                    v___y_1656_ = v___x_1719_;
                    v___y_1657_ = v___y_1690_;
                    v___y_1658_ = v___x_1718_;
                    v___y_1659_ = v___x_1716_;
                    v___y_1660_ = v___x_1721_;
                    v___y_1661_ = v___y_1694_;
                    v___y_1662_ = v___y_1698_;
                    v___y_1663_ = v___y_1689_;
                    v___y_1664_ = v___y_1692_;
                    v___y_1665_ = v___y_1695_;
                    v___y_1666_ = v___x_1711_;
                    v___y_1667_ = v___x_1713_;
                    v___y_1668_ = v___x_1714_;
                    v___y_1669_ = v___x_1723_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1697_);
                    v___x_1724_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                    v___y_1656_ = v___x_1719_;
                    v___y_1657_ = v___y_1690_;
                    v___y_1658_ = v___x_1718_;
                    v___y_1659_ = v___x_1716_;
                    v___y_1660_ = v___x_1721_;
                    v___y_1661_ = v___y_1694_;
                    v___y_1662_ = v___y_1698_;
                    v___y_1663_ = v___y_1689_;
                    v___y_1664_ = v___y_1692_;
                    v___y_1665_ = v___y_1695_;
                    v___y_1666_ = v___x_1711_;
                    v___y_1667_ = v___x_1713_;
                    v___y_1668_ = v___x_1714_;
                    v___y_1669_ = v___x_1724_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1731_ = lean_unsigned_to_nat(4);
                v___x_1732_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1731_);
                v___x_1733_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                lean_inc(v___x_1732_);
                v___x_1734_ = l_Lean_Syntax_isOfKind(v___x_1732_, v___x_1733_);
                if v___x_1734_ == 0 {
                    lean_dec(v___x_1732_);
                    lean_dec(v_phase_x3f_1728_);
                    lean_dec(v___y_1727_);
                    lean_dec(v___y_1726_);
                    lean_dec(v_x_1652_);
                    v___x_1735_ = lean_box(1);
                    v___x_1736_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                    lean_ctor_set(v___x_1736_, 1, v___y_1730_);
                    return v___x_1736_;
                } else {
                    v_ref_1737_ = lean_ctor_get(v___y_1729_, 5);
                    v___x_1738_ = lean_unsigned_to_nat(6);
                    v___x_1739_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1738_);
                    v___x_1740_ = lean_unsigned_to_nat(9);
                    v___x_1741_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1740_);
                    lean_dec(v_x_1652_);
                    v___x_1742_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                    v___x_1743_ = 0;
                    v___x_1744_ = l_Lean_SourceInfo_fromRef(v_ref_1737_, v___x_1743_);
                    v___x_1745_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1746_ = l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_1747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if lean_obj_tag(v___y_1727_) == 1 {
                        v_val_1748_ = lean_ctor_get(v___y_1727_, 0);
                        lean_inc(v_val_1748_);
                        lean_dec_ref_known(v___y_1727_, 1);
                        v___x_1749_ = l_Array_mkArray1___redArg(v_val_1748_);
                        v___y_1689_ = v___x_1747_;
                        v___y_1690_ = v___y_1730_;
                        v___y_1691_ = v___x_1741_;
                        v___y_1692_ = v___x_1745_;
                        v___y_1693_ = v___x_1746_;
                        v___y_1694_ = v___x_1744_;
                        v___y_1695_ = v___x_1732_;
                        v___y_1696_ = v___x_1739_;
                        v___y_1697_ = v_phase_x3f_1728_;
                        v___y_1698_ = v___y_1726_;
                        v___y_1699_ = v___x_1742_;
                        v___y_1700_ = v___x_1749_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_1727_);
                        v___x_1750_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1689_ = v___x_1747_;
                        v___y_1690_ = v___y_1730_;
                        v___y_1691_ = v___x_1741_;
                        v___y_1692_ = v___x_1745_;
                        v___y_1693_ = v___x_1746_;
                        v___y_1694_ = v___x_1744_;
                        v___y_1695_ = v___x_1732_;
                        v___y_1696_ = v___x_1739_;
                        v___y_1697_ = v_phase_x3f_1728_;
                        v___y_1698_ = v___y_1726_;
                        v___y_1699_ = v___x_1742_;
                        v___y_1700_ = v___x_1750_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1755_ = lean_unsigned_to_nat(1);
                v___x_1756_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1755_);
                v___x_1757_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7;
                lean_inc(v___x_1756_);
                v___x_1758_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1757_);
                if v___x_1758_ == 0 {
                    lean_dec(v___x_1756_);
                    lean_dec(v_doc_x3f_1752_);
                    lean_dec(v_x_1652_);
                    v___x_1759_ = lean_box(1);
                    v___x_1760_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1760_, 0, v___x_1759_);
                    lean_ctor_set(v___x_1760_, 1, v___y_1754_);
                    return v___x_1760_;
                } else {
                    v___x_1761_ = lean_unsigned_to_nat(3);
                    v___x_1762_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1761_);
                    v___x_1763_ = l_Lean_Syntax_isNone(v___x_1762_);
                    if v___x_1763_ == 0 {
                        lean_inc(v___x_1762_);
                        v___x_1764_ = l_Lean_Syntax_matchesNull(v___x_1762_, v___x_1755_);
                        if v___x_1764_ == 0 {
                            lean_dec(v___x_1762_);
                            lean_dec(v___x_1756_);
                            lean_dec(v_doc_x3f_1752_);
                            lean_dec(v_x_1652_);
                            v___x_1765_ = lean_box(1);
                            v___x_1766_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1766_, 0, v___x_1765_);
                            lean_ctor_set(v___x_1766_, 1, v___y_1754_);
                            return v___x_1766_;
                        } else {
                            v_phase_x3f_1767_ = l_Lean_Syntax_getArg(v___x_1762_, v___x_1687_);
                            lean_dec(v___x_1762_);
                            v___x_1768_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1768_, 0, v_phase_x3f_1767_);
                            v___y_1726_ = v___x_1756_;
                            v___y_1727_ = v_doc_x3f_1752_;
                            v_phase_x3f_1728_ = v___x_1768_;
                            v___y_1729_ = v___y_1753_;
                            v___y_1730_ = v___y_1754_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1762_);
                        v___x_1769_ = lean_box(0);
                        v___y_1726_ = v___x_1756_;
                        v___y_1727_ = v_doc_x3f_1752_;
                        v_phase_x3f_1728_ = v___x_1769_;
                        v___y_1729_ = v___y_1753_;
                        v___y_1730_ = v___y_1754_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(
    mut v_x_1783_: *mut LeanObject,
    mut v_a_1784_: *mut LeanObject,
    mut v_a_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1786_: *mut LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(v_x_1783_, v_a_1784_, v_a_1785_);
    lean_dec_ref(v_a_1784_);
    return v_res_1786_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__();
    lean_mark_persistent(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__);
    l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__();
    lean_mark_persistent(
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_Attr_cbvSimprocAttr = _init_l_Lean_Parser_Attr_cbvSimprocAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocAttr);
    l_Lean_Parser_Attr_cbvSimprocBuiltinAttr = _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr();
    lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_CbvSimproc(builtin);
}

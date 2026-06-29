// Lean compiler output
// Module: Lean.Elab.BindersUtil
// Imports: Lean.Parser.Term Lean.Parser.Term Lean.Parser.Do Init.Syntax
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone, l_Lean_mkHole,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_firstFrontendMacroScope,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isImplementationDetail;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0],
};
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16529391333736644786 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11514550152210403337 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [119, 105, 116, 104, 0],
};
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 111, 77, 97, 116, 99, 104, 0],
};
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            4365236509002904093 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0],
};
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__5_value)
                as *mut crate::leanh::LeanObject,
            13242179749370575553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 108, 101, 97, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_shouldExpandMatchAlt___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,1882088801735261575 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 108, 101, 97, 114, 37, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_clearInMatchAlt___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_clearInMatchAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_clearInMatchAlt___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_clearInMatchAlt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_LocalDeclKind_ofBinderName(
    mut v_binderName_755_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_756_: u8 = 0;
    v___x_756_ = l_Lean_Name_isImplementationDetail(v_binderName_755_);
    if v___x_756_ == 0 {
        let mut v___x_757_: u8 = 0;
        v___x_757_ = 0;
        return v___x_757_;
    } else {
        let mut v___x_758_: u8 = 0;
        v___x_758_ = 1;
        return v___x_758_;
    }
}
pub unsafe fn l_Lean_LocalDeclKind_ofBinderName___boxed(
    mut v_binderName_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_LocalDeclKind_ofBinderName(v_binderName_759_);
    crate::leanh::lean_dec(v_binderName_759_);
    v_r_761_ = crate::leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_Lean_Elab_Term_expandOptType(
    mut v_ref_762_: *mut crate::leanh::LeanObject,
    mut v_optType_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_764_: u8 = 0;
    v___x_764_ = l_Lean_Syntax_isNone(v_optType_763_);
    if v___x_764_ == 0 {
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_765_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_766_ = l_Lean_Syntax_getArg(v_optType_763_, v___x_765_);
        v___x_767_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_768_ = l_Lean_Syntax_getArg(v___x_766_, v___x_767_);
        crate::leanh::lean_dec(v___x_766_);
        return v___x_768_;
    } else {
        let mut v___x_769_: u8 = 0;
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_769_ = 0;
        v___x_770_ = l_Lean_mkHole(v_ref_762_, v___x_769_);
        return v___x_770_;
    }
}
pub unsafe fn l_Lean_Elab_Term_expandOptType___boxed(
    mut v_ref_771_: *mut crate::leanh::LeanObject,
    mut v_optType_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_Elab_Term_expandOptType(v_ref_771_, v_optType_772_);
    crate::leanh::lean_dec(v_optType_772_);
    crate::leanh::lean_dec(v_ref_771_);
    return v_res_773_;
}
pub unsafe fn l_Lean_Elab_Term_getMatchAltsNumPatterns(
    mut v_matchAlts_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alt0_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pats_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_776_ = l_Lean_Syntax_getArg(v_matchAlts_774_, v___x_775_);
    v_alt0_777_ = l_Lean_Syntax_getArg(v___x_776_, v___x_775_);
    crate::leanh::lean_dec(v___x_776_);
    v___x_778_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_779_ = l_Lean_Syntax_getArg(v_alt0_777_, v___x_778_);
    crate::leanh::lean_dec(v_alt0_777_);
    v___x_780_ = l_Lean_Syntax_getArg(v___x_779_, v___x_775_);
    crate::leanh::lean_dec(v___x_779_);
    v_pats_781_ = l_Lean_Syntax_getSepArgs(v___x_780_);
    crate::leanh::lean_dec(v___x_780_);
    v___x_782_ = lean_array_get_size(v_pats_781_);
    crate::leanh::lean_dec_ref(v_pats_781_);
    return v___x_782_;
}
pub unsafe fn l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(
    mut v_matchAlts_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_Elab_Term_getMatchAltsNumPatterns(v_matchAlts_783_);
    crate::leanh::lean_dec(v_matchAlts_783_);
    return v_res_784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(
    mut v___x_788_: *mut crate::leanh::LeanObject,
    mut v_sz_789_: usize,
    mut v_i_790_: usize,
    mut v_bs_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: u8 = 0;
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: usize = 0;
    let mut v___x_804_: usize = 0;
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_792_ = lean_usize_dec_lt(v_i_790_, v_sz_789_);
                if v___x_792_ == 0 {
                    crate::leanh::lean_dec(v___x_788_);
                    return v_bs_791_;
                } else {
                    v___x_793_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_v_794_ = lean_array_uget(v_bs_791_, v_i_790_);
                    v___x_795_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_796_ = lean_array_uset(v_bs_791_, v_i_790_, v___x_795_);
                    v___x_797_ = lean_mk_empty_array_with_capacity(v___x_793_);
                    v___x_798_ = lean_array_push(v___x_797_, v_v_794_);
                    v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1;
                    v___x_800_ = crate::leanh::lean_box(2);
                    v___x_801_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_801_, 0, v___x_800_);
                    crate::leanh::lean_ctor_set(v___x_801_, 1, v___x_799_);
                    crate::leanh::lean_ctor_set(v___x_801_, 2, v___x_798_);
                    crate::leanh::lean_inc(v___x_788_);
                    v___x_802_ = l_Lean_Syntax_setArg(v___x_788_, v___x_793_, v___x_801_);
                    v___x_803_ = 1usize;
                    v___x_804_ = lean_usize_add(v_i_790_, v___x_803_);
                    v___x_805_ = lean_array_uset(v_bs_x27_796_, v_i_790_, v___x_802_);
                    v_i_790_ = v___x_804_;
                    v_bs_791_ = v___x_805_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___boxed(
    mut v___x_807_: *mut crate::leanh::LeanObject,
    mut v_sz_808_: *mut crate::leanh::LeanObject,
    mut v_i_809_: *mut crate::leanh::LeanObject,
    mut v_bs_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_811_: usize = 0;
    let mut v_i_boxed_812_: usize = 0;
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_811_ = crate::leanh::lean_unbox_usize(v_sz_808_);
    crate::leanh::lean_dec(v_sz_808_);
    v_i_boxed_812_ = crate::leanh::lean_unbox_usize(v_i_809_);
    crate::leanh::lean_dec(v_i_809_);
    v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v___x_807_, v_sz_boxed_811_, v_i_boxed_812_, v_bs_810_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Elab_Term_expandMatchAlt(
    mut v_stx_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patss_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    v___x_815_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_816_ = l_Lean_Syntax_getArg(v_stx_814_, v___x_815_);
    v_patss_817_ = l_Lean_Syntax_getSepArgs(v___x_816_);
    crate::leanh::lean_dec(v___x_816_);
    v___x_818_ = lean_array_get_size(v_patss_817_);
    v___x_819_ = lean_nat_dec_le(v___x_818_, v___x_815_);
    if v___x_819_ == 0 {
        let mut v_sz_820_: usize = 0;
        let mut v___x_821_: usize = 0;
        let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_sz_820_ = lean_array_size(v_patss_817_);
        v___x_821_ = 0usize;
        v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0(v_stx_814_, v_sz_820_, v___x_821_, v_patss_817_);
        return v___x_822_;
    } else {
        let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_patss_817_);
        v___x_823_ = lean_mk_empty_array_with_capacity(v___x_815_);
        v___x_824_ = lean_array_push(v___x_823_, v_stx_814_);
        return v___x_824_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(
    mut v_sz_825_: usize,
    mut v_i_826_: usize,
    mut v_bs_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patss_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: usize = 0;
    let mut v___x_835_: usize = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_828_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
                if v___x_828_ == 0 {
                    v___x_829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_829_, 0, v_bs_827_);
                    return v___x_829_;
                } else {
                    v_v_830_ = lean_array_uget(v_bs_827_, v_i_826_);
                    v___x_831_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_832_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_831_);
                    v_patss_833_ = l_Lean_Syntax_getArgs(v_v_830_);
                    crate::leanh::lean_dec(v_v_830_);
                    v___x_834_ = 1usize;
                    v___x_835_ = lean_usize_add(v_i_826_, v___x_834_);
                    v___x_836_ = lean_array_uset(v_bs_x27_832_, v_i_826_, v_patss_833_);
                    v_i_826_ = v___x_835_;
                    v_bs_827_ = v___x_836_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0___boxed(
    mut v_sz_838_: *mut crate::leanh::LeanObject,
    mut v_i_839_: *mut crate::leanh::LeanObject,
    mut v_bs_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_841_: usize = 0;
    let mut v_i_boxed_842_: usize = 0;
    let mut v_res_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_841_ = crate::leanh::lean_unbox_usize(v_sz_838_);
    crate::leanh::lean_dec(v_sz_838_);
    v_i_boxed_842_ = crate::leanh::lean_unbox_usize(v_i_839_);
    crate::leanh::lean_dec(v_i_839_);
    v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_boxed_841_, v_i_boxed_842_, v_bs_840_);
    return v_res_843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(
    mut v___x_844_: u8,
    mut v_as_845_: *mut crate::leanh::LeanObject,
    mut v_i_846_: usize,
    mut v_stop_847_: usize,
    mut v_b_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: usize = 0;
    let mut v___x_854_: u8 = 0;
    let mut v_fst_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: u8 = 0;
    let mut v_snd_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v_unused_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut v_unused_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_854_ = lean_usize_dec_eq(v_i_846_, v_stop_847_);
                if v___x_854_ == 0 {
                    v_fst_855_ = crate::leanh::lean_ctor_get(v_b_848_, 0);
                    v___x_856_ = (crate::leanh::lean_unbox(v_fst_855_) as u8);
                    if v___x_856_ == 0 {
                        v_snd_857_ = crate::leanh::lean_ctor_get(v_b_848_, 1);
                        v_isSharedCheck_865_ = (!crate::leanh::lean_is_exclusive(v_b_848_)) as u8;
                        if v_isSharedCheck_865_ == 0 {
                            v_unused_866_ = crate::leanh::lean_ctor_get(v_b_848_, 0);
                            crate::leanh::lean_dec(v_unused_866_);
                            v___x_859_ = v_b_848_;
                            v_isShared_860_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_857_);
                            crate::leanh::lean_dec(v_b_848_);
                            v___x_859_ = crate::leanh::lean_box(0);
                            v_isShared_860_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_867_ = crate::leanh::lean_ctor_get(v_b_848_, 1);
                        v_isSharedCheck_877_ = (!crate::leanh::lean_is_exclusive(v_b_848_)) as u8;
                        if v_isSharedCheck_877_ == 0 {
                            v_unused_878_ = crate::leanh::lean_ctor_get(v_b_848_, 0);
                            crate::leanh::lean_dec(v_unused_878_);
                            v___x_869_ = v_b_848_;
                            v_isShared_870_ = v_isSharedCheck_877_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_867_);
                            crate::leanh::lean_dec(v_b_848_);
                            v___x_869_ = crate::leanh::lean_box(0);
                            v_isShared_870_ = v_isSharedCheck_877_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_848_;
                }
            }
            1 => {
                v___x_851_ = 1usize;
                v___x_852_ = lean_usize_add(v_i_846_, v___x_851_);
                v_i_846_ = v___x_852_;
                v_b_848_ = v___y_850_;
                state = 0;
                continue;
            }
            2 => {
                v___x_861_ = crate::leanh::lean_box((v___x_844_) as usize);
                if v_isShared_860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_861_);
                    v___x_863_ = v___x_859_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_857_);
                    v___x_863_ = v_reuseFailAlloc_864_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_850_ = v___x_863_;
                state = 1;
                continue;
            }
            4 => {
                v___x_871_ = lean_array_uget_borrowed(v_as_845_, v_i_846_);
                crate::leanh::lean_inc(v___x_871_);
                v___x_872_ = lean_array_push(v_snd_867_, v___x_871_);
                v___x_873_ = crate::leanh::lean_box((v___x_854_) as usize);
                if v_isShared_870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_872_);
                    crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_873_);
                    v___x_875_ = v___x_869_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_872_);
                    v___x_875_ = v_reuseFailAlloc_876_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_850_ = v___x_875_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1___boxed(
    mut v___x_879_: *mut crate::leanh::LeanObject,
    mut v_as_880_: *mut crate::leanh::LeanObject,
    mut v_i_881_: *mut crate::leanh::LeanObject,
    mut v_stop_882_: *mut crate::leanh::LeanObject,
    mut v_b_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_530__boxed_884_: u8 = 0;
    let mut v_i_boxed_885_: usize = 0;
    let mut v_stop_boxed_886_: usize = 0;
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_530__boxed_884_ = (crate::leanh::lean_unbox(v___x_879_) as u8);
    v_i_boxed_885_ = crate::leanh::lean_unbox_usize(v_i_881_);
    crate::leanh::lean_dec(v_i_881_);
    v_stop_boxed_886_ = crate::leanh::lean_unbox_usize(v_stop_882_);
    crate::leanh::lean_dec(v_stop_882_);
    v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_530__boxed_884_, v_as_880_, v_i_boxed_885_, v_stop_boxed_886_, v_b_883_);
    crate::leanh::lean_dec_ref(v_as_880_);
    return v_res_887_;
}
pub unsafe fn l_Lean_Elab_Term_shouldExpandMatchAlt(
    mut v_x_899_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_905_: usize = 0;
    let mut v___x_906_: usize = 0;
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v_val_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: u8 = 0;
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: usize = 0;
    let mut v___x_922_: usize = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: usize = 0;
    let mut v___x_926_: usize = 0;
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_900_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__4;
                crate::leanh::lean_inc(v_x_899_);
                v___x_901_ = l_Lean_Syntax_isOfKind(v_x_899_, v___x_900_);
                if v___x_901_ == 0 {
                    crate::leanh::lean_dec(v_x_899_);
                    return v___x_901_;
                } else {
                    v___x_902_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_912_ = l_Lean_Syntax_getArg(v_x_899_, v___x_902_);
                    crate::leanh::lean_dec(v_x_899_);
                    v___x_913_ = l_Lean_Syntax_getArgs(v___x_912_);
                    crate::leanh::lean_dec(v___x_912_);
                    v___x_914_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_915_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                    v___x_916_ = lean_array_get_size(v___x_913_);
                    v___x_917_ = lean_nat_dec_lt(v___x_914_, v___x_916_);
                    if v___x_917_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_913_);
                        v___y_904_ = v___x_915_;
                        state = 1;
                        continue;
                    } else {
                        v___x_918_ = crate::leanh::lean_box((v___x_901_) as usize);
                        v___x_919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
                        crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_915_);
                        v___x_920_ = lean_nat_dec_le(v___x_916_, v___x_916_);
                        if v___x_920_ == 0 {
                            if v___x_917_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_919_, 2);
                                crate::leanh::lean_dec_ref(v___x_913_);
                                v___y_904_ = v___x_915_;
                                state = 1;
                                continue;
                            } else {
                                v___x_921_ = 0usize;
                                v___x_922_ = lean_usize_of_nat(v___x_916_);
                                v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_901_, v___x_913_, v___x_921_, v___x_922_, v___x_919_);
                                crate::leanh::lean_dec_ref(v___x_913_);
                                v_snd_924_ = crate::leanh::lean_ctor_get(v___x_923_, 1);
                                crate::leanh::lean_inc(v_snd_924_);
                                crate::leanh::lean_dec_ref(v___x_923_);
                                v___y_904_ = v_snd_924_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_925_ = 0usize;
                            v___x_926_ = lean_usize_of_nat(v___x_916_);
                            v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__1(v___x_901_, v___x_913_, v___x_925_, v___x_926_, v___x_919_);
                            crate::leanh::lean_dec_ref(v___x_913_);
                            v_snd_928_ = crate::leanh::lean_ctor_get(v___x_927_, 1);
                            crate::leanh::lean_inc(v_snd_928_);
                            crate::leanh::lean_dec_ref(v___x_927_);
                            v___y_904_ = v_snd_928_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_905_ = lean_array_size(v___y_904_);
                v___x_906_ = 0usize;
                v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_shouldExpandMatchAlt_spec__0(v_sz_905_, v___x_906_, v___y_904_);
                if crate::leanh::lean_obj_tag(v___x_907_) == 0 {
                    v___x_908_ = 0;
                    return v___x_908_;
                } else {
                    v_val_909_ = crate::leanh::lean_ctor_get(v___x_907_, 0);
                    crate::leanh::lean_inc(v_val_909_);
                    crate::leanh::lean_dec_ref_known(v___x_907_, 1);
                    v___x_910_ = lean_array_get_size(v_val_909_);
                    crate::leanh::lean_dec(v_val_909_);
                    v___x_911_ = lean_nat_dec_lt(v___x_902_, v___x_910_);
                    return v___x_911_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(
    mut v_x_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_930_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v_x_929_);
    v_r_931_ = crate::leanh::lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(
    mut v_as_932_: *mut crate::leanh::LeanObject,
    mut v_i_933_: usize,
    mut v_stop_934_: usize,
    mut v_b_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: usize = 0;
    let mut v___x_942_: usize = 0;
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_937_ = lean_usize_dec_eq(v_i_933_, v_stop_934_);
                if v___x_937_ == 0 {
                    v___x_938_ = lean_array_uget_borrowed(v_as_932_, v_i_933_);
                    crate::leanh::lean_inc(v___x_938_);
                    v___x_939_ = l_Lean_Elab_Term_expandMatchAlt(v___x_938_);
                    v___x_940_ = l_Array_append___redArg(v_b_935_, v___x_939_);
                    crate::leanh::lean_dec_ref(v___x_939_);
                    v___x_941_ = 1usize;
                    v___x_942_ = lean_usize_add(v_i_933_, v___x_941_);
                    v_i_933_ = v___x_942_;
                    v_b_935_ = v___x_940_;
                    state = 0;
                    continue;
                } else {
                    v___x_944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_944_, 0, v_b_935_);
                    crate::leanh::lean_ctor_set(v___x_944_, 1, v___y_936_);
                    return v___x_944_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg___boxed(
    mut v_as_945_: *mut crate::leanh::LeanObject,
    mut v_i_946_: *mut crate::leanh::LeanObject,
    mut v_stop_947_: *mut crate::leanh::LeanObject,
    mut v_b_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_950_: usize = 0;
    let mut v_stop_boxed_951_: usize = 0;
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_950_ = crate::leanh::lean_unbox_usize(v_i_946_);
    crate::leanh::lean_dec(v_i_946_);
    v_stop_boxed_951_ = crate::leanh::lean_unbox_usize(v_stop_947_);
    crate::leanh::lean_dec(v_stop_947_);
    v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_945_, v_i_boxed_950_, v_stop_boxed_951_, v_b_948_, v___y_949_);
    crate::leanh::lean_dec_ref(v_as_945_);
    return v_res_952_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(
    mut v_as_953_: *mut crate::leanh::LeanObject,
    mut v_i_954_: usize,
    mut v_stop_955_: usize,
) -> u8 {
    let mut v___x_956_: u8 = 0;
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: usize = 0;
    let mut v___x_962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_956_ = lean_usize_dec_eq(v_i_954_, v_stop_955_);
                if v___x_956_ == 0 {
                    v___x_957_ = lean_array_uget_borrowed(v_as_953_, v_i_954_);
                    crate::leanh::lean_inc(v___x_957_);
                    v___x_958_ = l_Lean_Elab_Term_shouldExpandMatchAlt(v___x_957_);
                    if v___x_958_ == 0 {
                        v___x_959_ = 1usize;
                        v___x_960_ = lean_usize_add(v_i_954_, v___x_959_);
                        v_i_954_ = v___x_960_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_958_;
                    }
                } else {
                    v___x_962_ = 0;
                    return v___x_962_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0___boxed(
    mut v_as_963_: *mut crate::leanh::LeanObject,
    mut v_i_964_: *mut crate::leanh::LeanObject,
    mut v_stop_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_966_: usize = 0;
    let mut v_stop_boxed_967_: usize = 0;
    let mut v_res_968_: u8 = 0;
    let mut v_r_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_966_ = crate::leanh::lean_unbox_usize(v_i_964_);
    crate::leanh::lean_dec(v_i_964_);
    v_stop_boxed_967_ = crate::leanh::lean_unbox_usize(v_stop_965_);
    crate::leanh::lean_dec(v_stop_965_);
    v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_as_963_, v_i_boxed_966_, v_stop_boxed_967_);
    crate::leanh::lean_dec_ref(v_as_963_);
    v_r_969_ = crate::leanh::lean_box((v_res_968_) as usize);
    return v_r_969_;
}
pub unsafe fn l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(
    mut v_alts_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: usize = 0;
    let mut v___x_1000_: usize = 0;
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_996_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_997_ = lean_array_get_size(v_alts_972_);
                v___x_998_ = lean_nat_dec_lt(v___x_996_, v___x_997_);
                if v___x_998_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v___x_998_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_999_ = 0usize;
                        v___x_1000_ = lean_usize_of_nat(v___x_997_);
                        v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__0(v_alts_972_, v___x_999_, v___x_1000_);
                        if v___x_1001_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_1002_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___closed__0;
                            if v___x_998_ == 0 {
                                v_a_979_ = v___x_1002_;
                                v_a_980_ = v_a_974_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1003_ = lean_nat_dec_le(v___x_997_, v___x_997_);
                                if v___x_1003_ == 0 {
                                    if v___x_998_ == 0 {
                                        v_a_979_ = v___x_1002_;
                                        v_a_980_ = v_a_974_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_972_, v___x_999_, v___x_1000_, v___x_1002_, v_a_974_);
                                        v___y_984_ = v___x_1004_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_alts_972_, v___x_999_, v___x_1000_, v___x_1002_, v_a_974_);
                                    v___y_984_ = v___x_1005_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_976_ = crate::leanh::lean_box(0);
                v___x_977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
                crate::leanh::lean_ctor_set(v___x_977_, 1, v_a_974_);
                return v___x_977_;
            }
            2 => {
                v___x_981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_981_, 0, v_a_979_);
                v___x_982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
                crate::leanh::lean_ctor_set(v___x_982_, 1, v_a_980_);
                return v___x_982_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_984_) == 0 {
                    v_a_985_ = crate::leanh::lean_ctor_get(v___y_984_, 0);
                    crate::leanh::lean_inc(v_a_985_);
                    v_a_986_ = crate::leanh::lean_ctor_get(v___y_984_, 1);
                    crate::leanh::lean_inc(v_a_986_);
                    crate::leanh::lean_dec_ref_known(v___y_984_, 2);
                    v_a_979_ = v_a_985_;
                    v_a_980_ = v_a_986_;
                    state = 2;
                    continue;
                } else {
                    v_a_987_ = crate::leanh::lean_ctor_get(v___y_984_, 0);
                    v_a_988_ = crate::leanh::lean_ctor_get(v___y_984_, 1);
                    v_isSharedCheck_995_ = (!crate::leanh::lean_is_exclusive(v___y_984_)) as u8;
                    if v_isSharedCheck_995_ == 0 {
                        v___x_990_ = v___y_984_;
                        v_isShared_991_ = v_isSharedCheck_995_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_988_);
                        crate::leanh::lean_inc(v_a_987_);
                        crate::leanh::lean_dec(v___y_984_);
                        v___x_990_ = crate::leanh::lean_box(0);
                        v_isShared_991_ = v_isSharedCheck_995_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_991_ == 0 {
                    v___x_993_ = v___x_990_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 1, v_a_988_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand___boxed(
    mut v_alts_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(
        v_alts_1006_,
        v_a_1007_,
        v_a_1008_,
    );
    crate::leanh::lean_dec_ref(v_a_1007_);
    crate::leanh::lean_dec_ref(v_alts_1006_);
    return v_res_1009_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(
    mut v_as_1010_: *mut crate::leanh::LeanObject,
    mut v_i_1011_: usize,
    mut v_stop_1012_: usize,
    mut v_b_1013_: *mut crate::leanh::LeanObject,
    mut v___y_1014_: *mut crate::leanh::LeanObject,
    mut v___y_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___redArg(v_as_1010_, v_i_1011_, v_stop_1012_, v_b_1013_, v___y_1015_);
    return v___x_1016_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1___boxed(
    mut v_as_1017_: *mut crate::leanh::LeanObject,
    mut v_i_1018_: *mut crate::leanh::LeanObject,
    mut v_stop_1019_: *mut crate::leanh::LeanObject,
    mut v_b_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1023_: usize = 0;
    let mut v_stop_boxed_1024_: usize = 0;
    let mut v_res_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1023_ = crate::leanh::lean_unbox_usize(v_i_1018_);
    crate::leanh::lean_dec(v_i_1018_);
    v_stop_boxed_1024_ = crate::leanh::lean_unbox_usize(v_stop_1019_);
    crate::leanh::lean_dec(v_stop_1019_);
    v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand_spec__1(v_as_1017_, v_i_boxed_1023_, v_stop_boxed_1024_, v_b_1020_, v___y_1021_, v___y_1022_);
    crate::leanh::lean_dec_ref(v___y_1021_);
    crate::leanh::lean_dec_ref(v_as_1017_);
    return v_res_1025_;
}
pub unsafe fn _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1045_;
}
pub unsafe fn l_Lean_Elab_Term_expandMatchAlts_x3f(
    mut v_stx_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1162_: u8 = 0;
    let mut v_unused_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dep_x3f_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dep_x3f_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut v_unused_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: u8 = 0;
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut v___x_1303_: u8 = 0;
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1049_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0;
                v___x_1050_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
                crate::leanh::lean_inc(v_stx_1046_);
                v___x_1074_ = l_Lean_Syntax_isOfKind(v_stx_1046_, v___x_1050_);
                if v___x_1074_ == 0 {
                    v___x_1075_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__4;
                    crate::leanh::lean_inc(v_stx_1046_);
                    v___x_1100_ = l_Lean_Syntax_isOfKind(v_stx_1046_, v___x_1075_);
                    if v___x_1100_ == 0 {
                        crate::leanh::lean_dec(v_stx_1046_);
                        v___x_1101_ = crate::leanh::lean_box(0);
                        v___x_1102_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
                        crate::leanh::lean_ctor_set(v___x_1102_, 1, v_a_1048_);
                        return v___x_1102_;
                    } else {
                        v___x_1103_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1186_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1214_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1186_);
                        v___x_1215_ = l_Lean_Syntax_isNone(v___x_1214_);
                        if v___x_1215_ == 0 {
                            crate::leanh::lean_inc(v___x_1214_);
                            v___x_1216_ = l_Lean_Syntax_matchesNull(v___x_1214_, v___x_1186_);
                            if v___x_1216_ == 0 {
                                crate::leanh::lean_dec(v___x_1214_);
                                crate::leanh::lean_dec(v_stx_1046_);
                                v___x_1217_ = crate::leanh::lean_box(0);
                                v___x_1218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1218_, 0, v___x_1217_);
                                crate::leanh::lean_ctor_set(v___x_1218_, 1, v_a_1048_);
                                return v___x_1218_;
                            } else {
                                v_dep_x3f_1219_ = l_Lean_Syntax_getArg(v___x_1214_, v___x_1103_);
                                crate::leanh::lean_dec(v___x_1214_);
                                v___x_1220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1220_, 0, v_dep_x3f_1219_);
                                v_dep_x3f_1202_ = v___x_1220_;
                                v___y_1203_ = v_a_1047_;
                                v___y_1204_ = v_a_1048_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1214_);
                            v___x_1221_ = crate::leanh::lean_box(0);
                            v_dep_x3f_1202_ = v___x_1221_;
                            v___y_1203_ = v_a_1047_;
                            v___y_1204_ = v_a_1048_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v___x_1222_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1287_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1301_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1287_);
                    v___x_1302_ = l_Lean_Syntax_isNone(v___x_1301_);
                    if v___x_1302_ == 0 {
                        crate::leanh::lean_inc(v___x_1301_);
                        v___x_1303_ = l_Lean_Syntax_matchesNull(v___x_1301_, v___x_1287_);
                        if v___x_1303_ == 0 {
                            crate::leanh::lean_dec(v___x_1301_);
                            crate::leanh::lean_dec(v_stx_1046_);
                            v___x_1304_ = crate::leanh::lean_box(0);
                            v___x_1305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
                            crate::leanh::lean_ctor_set(v___x_1305_, 1, v_a_1048_);
                            return v___x_1305_;
                        } else {
                            v_gen_1306_ = l_Lean_Syntax_getArg(v___x_1301_, v___x_1222_);
                            crate::leanh::lean_dec(v___x_1301_);
                            v___x_1307_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1307_, 0, v_gen_1306_);
                            v_gen_1289_ = v___x_1307_;
                            v___y_1290_ = v_a_1047_;
                            v___y_1291_ = v_a_1048_;
                            state = 18;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1301_);
                        v___x_1308_ = crate::leanh::lean_box(0);
                        v_gen_1289_ = v___x_1308_;
                        v___y_1290_ = v_a_1047_;
                        v___y_1291_ = v_a_1048_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_1053_, 3);
                v___x_1062_ = l_Array_append___redArg(v___y_1053_, v___y_1061_);
                crate::leanh::lean_dec_ref(v___y_1061_);
                crate::leanh::lean_inc_n(v___y_1057_, 3);
                crate::leanh::lean_inc_n(v___y_1058_, 5);
                v___x_1063_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1063_, 0, v___y_1058_);
                crate::leanh::lean_ctor_set(v___x_1063_, 1, v___y_1057_);
                crate::leanh::lean_ctor_set(v___x_1063_, 2, v___x_1062_);
                v___x_1064_ = l_Array_append___redArg(v___y_1053_, v___y_1055_);
                crate::leanh::lean_dec_ref(v___y_1055_);
                v___x_1065_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1065_, 0, v___y_1058_);
                crate::leanh::lean_ctor_set(v___x_1065_, 1, v___y_1057_);
                crate::leanh::lean_ctor_set(v___x_1065_, 2, v___x_1064_);
                v___x_1066_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2;
                v___x_1067_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1067_, 0, v___y_1058_);
                crate::leanh::lean_ctor_set(v___x_1067_, 1, v___x_1066_);
                v___x_1068_ = l_Array_append___redArg(v___y_1053_, v___y_1060_);
                crate::leanh::lean_dec_ref(v___y_1060_);
                v___x_1069_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1069_, 0, v___y_1058_);
                crate::leanh::lean_ctor_set(v___x_1069_, 1, v___y_1057_);
                crate::leanh::lean_ctor_set(v___x_1069_, 2, v___x_1068_);
                crate::leanh::lean_inc(v___y_1056_);
                v___x_1070_ = l_Lean_Syntax_node1(v___y_1058_, v___y_1056_, v___x_1069_);
                v___x_1071_ = l_Lean_Syntax_node6(
                    v___y_1058_,
                    v___x_1050_,
                    v___y_1059_,
                    v___y_1054_,
                    v___x_1063_,
                    v___x_1065_,
                    v___x_1067_,
                    v___x_1070_,
                );
                v___x_1072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
                v___x_1073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1072_);
                crate::leanh::lean_ctor_set(v___x_1073_, 1, v___y_1052_);
                return v___x_1073_;
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_1082_, 3);
                v___x_1088_ = l_Array_append___redArg(v___y_1082_, v___y_1087_);
                crate::leanh::lean_dec_ref(v___y_1087_);
                crate::leanh::lean_inc_n(v___y_1085_, 3);
                crate::leanh::lean_inc_n(v___y_1086_, 5);
                v___x_1089_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1089_, 0, v___y_1086_);
                crate::leanh::lean_ctor_set(v___x_1089_, 1, v___y_1085_);
                crate::leanh::lean_ctor_set(v___x_1089_, 2, v___x_1088_);
                v___x_1090_ = l_Array_append___redArg(v___y_1082_, v___y_1083_);
                crate::leanh::lean_dec_ref(v___y_1083_);
                v___x_1091_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1091_, 0, v___y_1086_);
                crate::leanh::lean_ctor_set(v___x_1091_, 1, v___y_1085_);
                crate::leanh::lean_ctor_set(v___x_1091_, 2, v___x_1090_);
                v___x_1092_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2;
                v___x_1093_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1093_, 0, v___y_1086_);
                crate::leanh::lean_ctor_set(v___x_1093_, 1, v___x_1092_);
                v___x_1094_ = l_Array_append___redArg(v___y_1082_, v___y_1081_);
                crate::leanh::lean_dec_ref(v___y_1081_);
                v___x_1095_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1095_, 0, v___y_1086_);
                crate::leanh::lean_ctor_set(v___x_1095_, 1, v___y_1085_);
                crate::leanh::lean_ctor_set(v___x_1095_, 2, v___x_1094_);
                crate::leanh::lean_inc(v___y_1084_);
                v___x_1096_ = l_Lean_Syntax_node1(v___y_1086_, v___y_1084_, v___x_1095_);
                v___x_1097_ = l_Lean_Syntax_node7(
                    v___y_1086_,
                    v___x_1075_,
                    v___y_1080_,
                    v___y_1078_,
                    v___y_1079_,
                    v___x_1089_,
                    v___x_1091_,
                    v___x_1093_,
                    v___x_1096_,
                );
                v___x_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1098_, 0, v___x_1097_);
                v___x_1099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1099_, 0, v___x_1098_);
                crate::leanh::lean_ctor_set(v___x_1099_, 1, v___y_1077_);
                return v___x_1099_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v___y_1109_);
                v___x_1116_ = l_Array_append___redArg(v___y_1109_, v___y_1115_);
                crate::leanh::lean_dec_ref(v___y_1115_);
                crate::leanh::lean_inc(v___y_1112_);
                crate::leanh::lean_inc(v___y_1113_);
                v___x_1117_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1117_, 0, v___y_1113_);
                crate::leanh::lean_ctor_set(v___x_1117_, 1, v___y_1112_);
                crate::leanh::lean_ctor_set(v___x_1117_, 2, v___x_1116_);
                if crate::leanh::lean_obj_tag(v___y_1114_) == 1 {
                    v_val_1118_ = crate::leanh::lean_ctor_get(v___y_1114_, 0);
                    crate::leanh::lean_inc(v_val_1118_);
                    crate::leanh::lean_dec_ref_known(v___y_1114_, 1);
                    v___x_1119_ = l_Array_mkArray1___redArg(v_val_1118_);
                    v___y_1077_ = v___y_1106_;
                    v___y_1078_ = v___y_1105_;
                    v___y_1079_ = v___x_1117_;
                    v___y_1080_ = v___y_1108_;
                    v___y_1081_ = v___y_1107_;
                    v___y_1082_ = v___y_1109_;
                    v___y_1083_ = v___y_1110_;
                    v___y_1084_ = v___y_1111_;
                    v___y_1085_ = v___y_1112_;
                    v___y_1086_ = v___y_1113_;
                    v___y_1087_ = v___x_1119_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1114_);
                    v___x_1120_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                    v___y_1077_ = v___y_1106_;
                    v___y_1078_ = v___y_1105_;
                    v___y_1079_ = v___x_1117_;
                    v___y_1080_ = v___y_1108_;
                    v___y_1081_ = v___y_1107_;
                    v___y_1082_ = v___y_1109_;
                    v___y_1083_ = v___y_1110_;
                    v___y_1084_ = v___y_1111_;
                    v___y_1085_ = v___y_1112_;
                    v___y_1086_ = v___y_1113_;
                    v___y_1087_ = v___x_1120_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_1125_);
                v___x_1133_ = l_Array_append___redArg(v___y_1125_, v___y_1132_);
                crate::leanh::lean_dec_ref(v___y_1132_);
                crate::leanh::lean_inc(v___y_1128_);
                crate::leanh::lean_inc(v___y_1129_);
                v___x_1134_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1134_, 0, v___y_1129_);
                crate::leanh::lean_ctor_set(v___x_1134_, 1, v___y_1128_);
                crate::leanh::lean_ctor_set(v___x_1134_, 2, v___x_1133_);
                if crate::leanh::lean_obj_tag(v___y_1130_) == 1 {
                    v_val_1135_ = crate::leanh::lean_ctor_get(v___y_1130_, 0);
                    crate::leanh::lean_inc(v_val_1135_);
                    crate::leanh::lean_dec_ref_known(v___y_1130_, 1);
                    v___x_1136_ = l_Array_mkArray1___redArg(v_val_1135_);
                    v___y_1105_ = v___x_1134_;
                    v___y_1106_ = v___y_1122_;
                    v___y_1107_ = v___y_1124_;
                    v___y_1108_ = v___y_1123_;
                    v___y_1109_ = v___y_1125_;
                    v___y_1110_ = v___y_1126_;
                    v___y_1111_ = v___y_1127_;
                    v___y_1112_ = v___y_1128_;
                    v___y_1113_ = v___y_1129_;
                    v___y_1114_ = v___y_1131_;
                    v___y_1115_ = v___x_1136_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1130_);
                    v___x_1137_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                    v___y_1105_ = v___x_1134_;
                    v___y_1106_ = v___y_1122_;
                    v___y_1107_ = v___y_1124_;
                    v___y_1108_ = v___y_1123_;
                    v___y_1109_ = v___y_1125_;
                    v___y_1110_ = v___y_1126_;
                    v___y_1111_ = v___y_1127_;
                    v___y_1112_ = v___y_1128_;
                    v___y_1113_ = v___y_1129_;
                    v___y_1114_ = v___y_1131_;
                    v___y_1115_ = v___x_1137_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_1144_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_1145_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1144_);
                v___x_1146_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
                crate::leanh::lean_inc(v___x_1145_);
                v___x_1147_ = l_Lean_Syntax_isOfKind(v___x_1145_, v___x_1146_);
                if v___x_1147_ == 0 {
                    crate::leanh::lean_dec(v___x_1145_);
                    crate::leanh::lean_dec(v_motive_1141_);
                    crate::leanh::lean_dec(v___y_1140_);
                    crate::leanh::lean_dec(v___y_1139_);
                    crate::leanh::lean_dec(v_stx_1046_);
                    v___x_1148_ = crate::leanh::lean_box(0);
                    v___x_1149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1149_, 0, v___x_1148_);
                    crate::leanh::lean_ctor_set(v___x_1149_, 1, v___y_1143_);
                    return v___x_1149_;
                } else {
                    v___x_1150_ = l_Lean_Syntax_getArg(v___x_1145_, v___x_1103_);
                    crate::leanh::lean_dec(v___x_1145_);
                    v_alts_1151_ = l_Lean_Syntax_getArgs(v___x_1150_);
                    crate::leanh::lean_dec(v___x_1150_);
                    v___x_1152_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_1151_, v___y_1142_, v___y_1143_);
                    crate::leanh::lean_dec_ref(v_alts_1151_);
                    if crate::leanh::lean_obj_tag(v___x_1152_) == 0 {
                        v_a_1153_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                        crate::leanh::lean_inc(v_a_1153_);
                        if crate::leanh::lean_obj_tag(v_a_1153_) == 0 {
                            crate::leanh::lean_dec(v_motive_1141_);
                            crate::leanh::lean_dec(v___y_1140_);
                            crate::leanh::lean_dec(v___y_1139_);
                            crate::leanh::lean_dec(v_stx_1046_);
                            v_a_1154_ = crate::leanh::lean_ctor_get(v___x_1152_, 1);
                            v_isSharedCheck_1162_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1152_)) as u8;
                            if v_isSharedCheck_1162_ == 0 {
                                v_unused_1163_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                                crate::leanh::lean_dec(v_unused_1163_);
                                v___x_1156_ = v___x_1152_;
                                v_isShared_1157_ = v_isSharedCheck_1162_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1154_);
                                crate::leanh::lean_dec(v___x_1152_);
                                v___x_1156_ = crate::leanh::lean_box(0);
                                v_isShared_1157_ = v_isSharedCheck_1162_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_1164_ = crate::leanh::lean_ctor_get(v___x_1152_, 1);
                            crate::leanh::lean_inc(v_a_1164_);
                            crate::leanh::lean_dec_ref_known(v___x_1152_, 2);
                            v_val_1165_ = crate::leanh::lean_ctor_get(v_a_1153_, 0);
                            crate::leanh::lean_inc(v_val_1165_);
                            crate::leanh::lean_dec_ref_known(v_a_1153_, 1);
                            v_ref_1166_ = crate::leanh::lean_ctor_get(v___y_1142_, 5);
                            v___x_1167_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_1168_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1167_);
                            crate::leanh::lean_dec(v_stx_1046_);
                            v___x_1169_ = l_Lean_Syntax_getArgs(v___x_1168_);
                            crate::leanh::lean_dec(v___x_1168_);
                            v___x_1170_ = l_Lean_SourceInfo_fromRef(v_ref_1166_, v___x_1074_);
                            crate::leanh::lean_inc(v___x_1170_);
                            v___x_1171_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
                            crate::leanh::lean_ctor_set(v___x_1171_, 1, v___x_1049_);
                            v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1;
                            v___x_1173_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once
                                ),
                                _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7,
                            );
                            if crate::leanh::lean_obj_tag(v___y_1139_) == 1 {
                                v_val_1174_ = crate::leanh::lean_ctor_get(v___y_1139_, 0);
                                crate::leanh::lean_inc(v_val_1174_);
                                crate::leanh::lean_dec_ref_known(v___y_1139_, 1);
                                v___x_1175_ = l_Array_mkArray1___redArg(v_val_1174_);
                                v___y_1122_ = v_a_1164_;
                                v___y_1123_ = v___x_1171_;
                                v___y_1124_ = v_val_1165_;
                                v___y_1125_ = v___x_1173_;
                                v___y_1126_ = v___x_1169_;
                                v___y_1127_ = v___x_1146_;
                                v___y_1128_ = v___x_1172_;
                                v___y_1129_ = v___x_1170_;
                                v___y_1130_ = v___y_1140_;
                                v___y_1131_ = v_motive_1141_;
                                v___y_1132_ = v___x_1175_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_1139_);
                                v___x_1176_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                                v___y_1122_ = v_a_1164_;
                                v___y_1123_ = v___x_1171_;
                                v___y_1124_ = v_val_1165_;
                                v___y_1125_ = v___x_1173_;
                                v___y_1126_ = v___x_1169_;
                                v___y_1127_ = v___x_1146_;
                                v___y_1128_ = v___x_1172_;
                                v___y_1129_ = v___x_1170_;
                                v___y_1130_ = v___y_1140_;
                                v___y_1131_ = v_motive_1141_;
                                v___y_1132_ = v___x_1176_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_motive_1141_);
                        crate::leanh::lean_dec(v___y_1140_);
                        crate::leanh::lean_dec(v___y_1139_);
                        crate::leanh::lean_dec(v_stx_1046_);
                        v_a_1177_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                        v_a_1178_ = crate::leanh::lean_ctor_get(v___x_1152_, 1);
                        v_isSharedCheck_1185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1152_)) as u8;
                        if v_isSharedCheck_1185_ == 0 {
                            v___x_1180_ = v___x_1152_;
                            v_isShared_1181_ = v_isSharedCheck_1185_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1178_);
                            crate::leanh::lean_inc(v_a_1177_);
                            crate::leanh::lean_dec(v___x_1152_);
                            v___x_1180_ = crate::leanh::lean_box(0);
                            v_isShared_1181_ = v_isSharedCheck_1185_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_1158_ = crate::leanh::lean_box(0);
                if v_isShared_1157_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1158_);
                    v___x_1160_ = v___x_1156_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_a_1154_);
                    v___x_1160_ = v_reuseFailAlloc_1161_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1160_;
            }
            8 => {
                if v_isShared_1181_ == 0 {
                    v___x_1183_ = v___x_1180_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1178_);
                    v___x_1183_ = v_reuseFailAlloc_1184_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1183_;
            }
            10 => {
                v___x_1192_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1193_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1192_);
                v___x_1194_ = l_Lean_Syntax_isNone(v___x_1193_);
                if v___x_1194_ == 0 {
                    crate::leanh::lean_inc(v___x_1193_);
                    v___x_1195_ = l_Lean_Syntax_matchesNull(v___x_1193_, v___x_1186_);
                    if v___x_1195_ == 0 {
                        crate::leanh::lean_dec(v___x_1193_);
                        crate::leanh::lean_dec(v_gen_1189_);
                        crate::leanh::lean_dec(v___y_1188_);
                        crate::leanh::lean_dec(v_stx_1046_);
                        v___x_1196_ = crate::leanh::lean_box(0);
                        v___x_1197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1196_);
                        crate::leanh::lean_ctor_set(v___x_1197_, 1, v___y_1191_);
                        return v___x_1197_;
                    } else {
                        v_motive_1198_ = l_Lean_Syntax_getArg(v___x_1193_, v___x_1103_);
                        crate::leanh::lean_dec(v___x_1193_);
                        v___x_1199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1199_, 0, v_motive_1198_);
                        v___y_1139_ = v___y_1188_;
                        v___y_1140_ = v_gen_1189_;
                        v_motive_1141_ = v___x_1199_;
                        v___y_1142_ = v___y_1190_;
                        v___y_1143_ = v___y_1191_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1193_);
                    v___x_1200_ = crate::leanh::lean_box(0);
                    v___y_1139_ = v___y_1188_;
                    v___y_1140_ = v_gen_1189_;
                    v_motive_1141_ = v___x_1200_;
                    v___y_1142_ = v___y_1190_;
                    v___y_1143_ = v___y_1191_;
                    state = 5;
                    continue;
                }
            }
            11 => {
                v___x_1205_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1206_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1205_);
                v___x_1207_ = l_Lean_Syntax_isNone(v___x_1206_);
                if v___x_1207_ == 0 {
                    crate::leanh::lean_inc(v___x_1206_);
                    v___x_1208_ = l_Lean_Syntax_matchesNull(v___x_1206_, v___x_1186_);
                    if v___x_1208_ == 0 {
                        crate::leanh::lean_dec(v___x_1206_);
                        crate::leanh::lean_dec(v_dep_x3f_1202_);
                        crate::leanh::lean_dec(v_stx_1046_);
                        v___x_1209_ = crate::leanh::lean_box(0);
                        v___x_1210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1209_);
                        crate::leanh::lean_ctor_set(v___x_1210_, 1, v___y_1204_);
                        return v___x_1210_;
                    } else {
                        v_gen_1211_ = l_Lean_Syntax_getArg(v___x_1206_, v___x_1103_);
                        crate::leanh::lean_dec(v___x_1206_);
                        v___x_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1212_, 0, v_gen_1211_);
                        v___y_1188_ = v_dep_x3f_1202_;
                        v_gen_1189_ = v___x_1212_;
                        v___y_1190_ = v___y_1203_;
                        v___y_1191_ = v___y_1204_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1206_);
                    v___x_1213_ = crate::leanh::lean_box(0);
                    v___y_1188_ = v_dep_x3f_1202_;
                    v_gen_1189_ = v___x_1213_;
                    v___y_1190_ = v___y_1203_;
                    v___y_1191_ = v___y_1204_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v___y_1225_);
                v___x_1234_ = l_Array_append___redArg(v___y_1225_, v___y_1233_);
                crate::leanh::lean_dec_ref(v___y_1233_);
                crate::leanh::lean_inc(v___y_1229_);
                crate::leanh::lean_inc(v___y_1230_);
                v___x_1235_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1235_, 0, v___y_1230_);
                crate::leanh::lean_ctor_set(v___x_1235_, 1, v___y_1229_);
                crate::leanh::lean_ctor_set(v___x_1235_, 2, v___x_1234_);
                if crate::leanh::lean_obj_tag(v___y_1227_) == 1 {
                    v_val_1236_ = crate::leanh::lean_ctor_get(v___y_1227_, 0);
                    crate::leanh::lean_inc(v_val_1236_);
                    crate::leanh::lean_dec_ref_known(v___y_1227_, 1);
                    v___x_1237_ = l_Array_mkArray1___redArg(v_val_1236_);
                    v___y_1052_ = v___y_1224_;
                    v___y_1053_ = v___y_1225_;
                    v___y_1054_ = v___x_1235_;
                    v___y_1055_ = v___y_1226_;
                    v___y_1056_ = v___y_1228_;
                    v___y_1057_ = v___y_1229_;
                    v___y_1058_ = v___y_1230_;
                    v___y_1059_ = v___y_1232_;
                    v___y_1060_ = v___y_1231_;
                    v___y_1061_ = v___x_1237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1227_);
                    v___x_1238_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                    v___y_1052_ = v___y_1224_;
                    v___y_1053_ = v___y_1225_;
                    v___y_1054_ = v___x_1235_;
                    v___y_1055_ = v___y_1226_;
                    v___y_1056_ = v___y_1228_;
                    v___y_1057_ = v___y_1229_;
                    v___y_1058_ = v___y_1230_;
                    v___y_1059_ = v___y_1232_;
                    v___y_1060_ = v___y_1231_;
                    v___y_1061_ = v___x_1238_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                v___x_1244_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_1245_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1244_);
                v___x_1246_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
                crate::leanh::lean_inc(v___x_1245_);
                v___x_1247_ = l_Lean_Syntax_isOfKind(v___x_1245_, v___x_1246_);
                if v___x_1247_ == 0 {
                    crate::leanh::lean_dec(v___x_1245_);
                    crate::leanh::lean_dec(v_motive_1241_);
                    crate::leanh::lean_dec(v___y_1240_);
                    crate::leanh::lean_dec(v_stx_1046_);
                    v___x_1248_ = crate::leanh::lean_box(0);
                    v___x_1249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1248_);
                    crate::leanh::lean_ctor_set(v___x_1249_, 1, v___y_1243_);
                    return v___x_1249_;
                } else {
                    v___x_1250_ = l_Lean_Syntax_getArg(v___x_1245_, v___x_1222_);
                    crate::leanh::lean_dec(v___x_1245_);
                    v_alts_1251_ = l_Lean_Syntax_getArgs(v___x_1250_);
                    crate::leanh::lean_dec(v___x_1250_);
                    v___x_1252_ = l___private_Lean_Elab_BindersUtil_0__Lean_Elab_Term_expandMatchAlts_x3f_expand(v_alts_1251_, v___y_1242_, v___y_1243_);
                    crate::leanh::lean_dec_ref(v_alts_1251_);
                    if crate::leanh::lean_obj_tag(v___x_1252_) == 0 {
                        v_a_1253_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
                        crate::leanh::lean_inc(v_a_1253_);
                        if crate::leanh::lean_obj_tag(v_a_1253_) == 0 {
                            crate::leanh::lean_dec(v_motive_1241_);
                            crate::leanh::lean_dec(v___y_1240_);
                            crate::leanh::lean_dec(v_stx_1046_);
                            v_a_1254_ = crate::leanh::lean_ctor_get(v___x_1252_, 1);
                            v_isSharedCheck_1262_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1252_)) as u8;
                            if v_isSharedCheck_1262_ == 0 {
                                v_unused_1263_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
                                crate::leanh::lean_dec(v_unused_1263_);
                                v___x_1256_ = v___x_1252_;
                                v_isShared_1257_ = v_isSharedCheck_1262_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1254_);
                                crate::leanh::lean_dec(v___x_1252_);
                                v___x_1256_ = crate::leanh::lean_box(0);
                                v_isShared_1257_ = v_isSharedCheck_1262_;
                                state = 14;
                                continue;
                            }
                        } else {
                            v_a_1264_ = crate::leanh::lean_ctor_get(v___x_1252_, 1);
                            crate::leanh::lean_inc(v_a_1264_);
                            crate::leanh::lean_dec_ref_known(v___x_1252_, 2);
                            v_val_1265_ = crate::leanh::lean_ctor_get(v_a_1253_, 0);
                            crate::leanh::lean_inc(v_val_1265_);
                            crate::leanh::lean_dec_ref_known(v_a_1253_, 1);
                            v_ref_1266_ = crate::leanh::lean_ctor_get(v___y_1242_, 5);
                            v___x_1267_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1268_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1267_);
                            crate::leanh::lean_dec(v_stx_1046_);
                            v___x_1269_ = l_Lean_Syntax_getArgs(v___x_1268_);
                            crate::leanh::lean_dec(v___x_1268_);
                            v___x_1270_ = 0;
                            v___x_1271_ = l_Lean_SourceInfo_fromRef(v_ref_1266_, v___x_1270_);
                            crate::leanh::lean_inc(v___x_1271_);
                            v___x_1272_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1272_, 0, v___x_1271_);
                            crate::leanh::lean_ctor_set(v___x_1272_, 1, v___x_1049_);
                            v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1;
                            v___x_1274_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once
                                ),
                                _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7,
                            );
                            if crate::leanh::lean_obj_tag(v___y_1240_) == 1 {
                                v_val_1275_ = crate::leanh::lean_ctor_get(v___y_1240_, 0);
                                crate::leanh::lean_inc(v_val_1275_);
                                crate::leanh::lean_dec_ref_known(v___y_1240_, 1);
                                v___x_1276_ = l_Array_mkArray1___redArg(v_val_1275_);
                                v___y_1224_ = v_a_1264_;
                                v___y_1225_ = v___x_1274_;
                                v___y_1226_ = v___x_1269_;
                                v___y_1227_ = v_motive_1241_;
                                v___y_1228_ = v___x_1246_;
                                v___y_1229_ = v___x_1273_;
                                v___y_1230_ = v___x_1271_;
                                v___y_1231_ = v_val_1265_;
                                v___y_1232_ = v___x_1272_;
                                v___y_1233_ = v___x_1276_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_1240_);
                                v___x_1277_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                                v___y_1224_ = v_a_1264_;
                                v___y_1225_ = v___x_1274_;
                                v___y_1226_ = v___x_1269_;
                                v___y_1227_ = v_motive_1241_;
                                v___y_1228_ = v___x_1246_;
                                v___y_1229_ = v___x_1273_;
                                v___y_1230_ = v___x_1271_;
                                v___y_1231_ = v_val_1265_;
                                v___y_1232_ = v___x_1272_;
                                v___y_1233_ = v___x_1277_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_motive_1241_);
                        crate::leanh::lean_dec(v___y_1240_);
                        crate::leanh::lean_dec(v_stx_1046_);
                        v_a_1278_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
                        v_a_1279_ = crate::leanh::lean_ctor_get(v___x_1252_, 1);
                        v_isSharedCheck_1286_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1252_)) as u8;
                        if v_isSharedCheck_1286_ == 0 {
                            v___x_1281_ = v___x_1252_;
                            v_isShared_1282_ = v_isSharedCheck_1286_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1279_);
                            crate::leanh::lean_inc(v_a_1278_);
                            crate::leanh::lean_dec(v___x_1252_);
                            v___x_1281_ = crate::leanh::lean_box(0);
                            v_isShared_1282_ = v_isSharedCheck_1286_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            14 => {
                v___x_1258_ = crate::leanh::lean_box(0);
                if v_isShared_1257_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1258_);
                    v___x_1260_ = v___x_1256_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_a_1254_);
                    v___x_1260_ = v_reuseFailAlloc_1261_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1260_;
            }
            16 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1284_;
            }
            18 => {
                v___x_1292_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1293_ = l_Lean_Syntax_getArg(v_stx_1046_, v___x_1292_);
                v___x_1294_ = l_Lean_Syntax_isNone(v___x_1293_);
                if v___x_1294_ == 0 {
                    crate::leanh::lean_inc(v___x_1293_);
                    v___x_1295_ = l_Lean_Syntax_matchesNull(v___x_1293_, v___x_1287_);
                    if v___x_1295_ == 0 {
                        crate::leanh::lean_dec(v___x_1293_);
                        crate::leanh::lean_dec(v_gen_1289_);
                        crate::leanh::lean_dec(v_stx_1046_);
                        v___x_1296_ = crate::leanh::lean_box(0);
                        v___x_1297_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
                        crate::leanh::lean_ctor_set(v___x_1297_, 1, v___y_1291_);
                        return v___x_1297_;
                    } else {
                        v_motive_1298_ = l_Lean_Syntax_getArg(v___x_1293_, v___x_1222_);
                        crate::leanh::lean_dec(v___x_1293_);
                        v___x_1299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1299_, 0, v_motive_1298_);
                        v___y_1240_ = v_gen_1289_;
                        v_motive_1241_ = v___x_1299_;
                        v___y_1242_ = v___y_1290_;
                        v___y_1243_ = v___y_1291_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1293_);
                    v___x_1300_ = crate::leanh::lean_box(0);
                    v___y_1240_ = v_gen_1289_;
                    v_motive_1241_ = v___x_1300_;
                    v___y_1242_ = v___y_1290_;
                    v___y_1243_ = v___y_1291_;
                    state = 13;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(
    mut v_stx_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l_Lean_Elab_Term_expandMatchAlts_x3f(v_stx_1309_, v_a_1310_, v_a_1311_);
    crate::leanh::lean_dec_ref(v_a_1310_);
    return v_res_1312_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(
    mut v_as_1321_: *mut crate::leanh::LeanObject,
    mut v_sz_1322_: usize,
    mut v_i_1323_: usize,
    mut v_b_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1327_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
                if v___x_1327_ == 0 {
                    v___x_1328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1328_, 0, v_b_1324_);
                    crate::leanh::lean_ctor_set(v___x_1328_, 1, v___y_1326_);
                    return v___x_1328_;
                } else {
                    v_ref_1329_ = crate::leanh::lean_ctor_get(v___y_1325_, 0);
                    v_a_1330_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
                    v___x_1331_ = 0;
                    v___x_1332_ = l_Lean_SourceInfo_fromRef(v_ref_1329_, v___x_1331_);
                    v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__1;
                    v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__2;
                    crate::leanh::lean_inc_n(v___x_1332_, 2);
                    v___x_1335_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1332_);
                    crate::leanh::lean_ctor_set(v___x_1335_, 1, v___x_1334_);
                    v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___closed__3;
                    v___x_1337_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1337_, 0, v___x_1332_);
                    crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1336_);
                    crate::leanh::lean_inc(v_a_1330_);
                    v___x_1338_ = l_Lean_Syntax_node4(
                        v___x_1332_,
                        v___x_1333_,
                        v___x_1335_,
                        v_a_1330_,
                        v___x_1337_,
                        v_b_1324_,
                    );
                    v___x_1339_ = 1usize;
                    v___x_1340_ = lean_usize_add(v_i_1323_, v___x_1339_);
                    v_i_1323_ = v___x_1340_;
                    v_b_1324_ = v___x_1338_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(
    mut v_as_1342_: *mut crate::leanh::LeanObject,
    mut v_sz_1343_: *mut crate::leanh::LeanObject,
    mut v_i_1344_: *mut crate::leanh::LeanObject,
    mut v_b_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1348_: usize = 0;
    let mut v_i_boxed_1349_: usize = 0;
    let mut v_res_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1348_ = crate::leanh::lean_unbox_usize(v_sz_1343_);
    crate::leanh::lean_dec(v_sz_1343_);
    v_i_boxed_1349_ = crate::leanh::lean_unbox_usize(v_i_1344_);
    crate::leanh::lean_dec(v_i_1344_);
    v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_as_1342_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1345_, v___y_1346_, v___y_1347_);
    crate::leanh::lean_dec_ref(v___y_1346_);
    crate::leanh::lean_dec_ref(v_as_1342_);
    return v_res_1350_;
}
pub unsafe fn _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_firstFrontendMacroScope;
    v___x_1352_ = crate::leanh::lean_box(0);
    v___x_1353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1353_, 0, v___x_1352_);
    crate::leanh::lean_ctor_set(v___x_1353_, 1, v___x_1351_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1355_ = l_Lean_firstFrontendMacroScope;
    v___x_1356_ = lean_nat_add(v___x_1355_, v___x_1354_);
    return v___x_1356_;
}
pub unsafe fn l_Lean_Elab_Term_clearInMatchAlt(
    mut v_stx_1357_: *mut crate::leanh::LeanObject,
    mut v_vars_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v_v_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v_unused_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_1357_) == 1 {
                    v_info_1359_ = crate::leanh::lean_ctor_get(v_stx_1357_, 0);
                    v_kind_1360_ = crate::leanh::lean_ctor_get(v_stx_1357_, 1);
                    v_args_1361_ = crate::leanh::lean_ctor_get(v_stx_1357_, 2);
                    v___x_1362_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1363_ = lean_array_get_size(v_args_1361_);
                    v___x_1364_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
                    if v___x_1364_ == 0 {
                        return v_stx_1357_;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_1361_);
                        crate::leanh::lean_inc(v_kind_1360_);
                        crate::leanh::lean_inc(v_info_1359_);
                        v_isSharedCheck_1381_ =
                            (!crate::leanh::lean_is_exclusive(v_stx_1357_)) as u8;
                        if v_isSharedCheck_1381_ == 0 {
                            v_unused_1382_ = crate::leanh::lean_ctor_get(v_stx_1357_, 2);
                            crate::leanh::lean_dec(v_unused_1382_);
                            v_unused_1383_ = crate::leanh::lean_ctor_get(v_stx_1357_, 1);
                            crate::leanh::lean_dec(v_unused_1383_);
                            v_unused_1384_ = crate::leanh::lean_ctor_get(v_stx_1357_, 0);
                            crate::leanh::lean_dec(v_unused_1384_);
                            v___x_1366_ = v_stx_1357_;
                            v_isShared_1367_ = v_isSharedCheck_1381_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_stx_1357_);
                            v___x_1366_ = crate::leanh::lean_box(0);
                            v_isShared_1367_ = v_isSharedCheck_1381_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_stx_1357_;
                }
            }
            1 => {
                v_v_1368_ = lean_array_fget_borrowed(v_args_1361_, v___x_1362_);
                v_sz_1369_ = lean_array_size(v_vars_1358_);
                v___x_1370_ = 0usize;
                v___x_1371_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_clearInMatchAlt___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_clearInMatchAlt___closed__0_once),
                    _init_l_Lean_Elab_Term_clearInMatchAlt___closed__0,
                );
                v___x_1372_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_clearInMatchAlt___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_clearInMatchAlt___closed__1_once),
                    _init_l_Lean_Elab_Term_clearInMatchAlt___closed__1,
                );
                crate::leanh::lean_inc(v_v_1368_);
                v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_clearInMatchAlt_spec__0(v_vars_1358_, v_sz_1369_, v___x_1370_, v_v_1368_, v___x_1371_, v___x_1372_);
                v_fst_1374_ = crate::leanh::lean_ctor_get(v___x_1373_, 0);
                crate::leanh::lean_inc(v_fst_1374_);
                crate::leanh::lean_dec_ref(v___x_1373_);
                v___x_1375_ = crate::leanh::lean_box(0);
                v_xs_x27_1376_ = lean_array_fset(v_args_1361_, v___x_1362_, v___x_1375_);
                v___x_1377_ = lean_array_fset(v_xs_x27_1376_, v___x_1362_, v_fst_1374_);
                if v_isShared_1367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1366_, 2, v___x_1377_);
                    v___x_1379_ = v___x_1366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_info_1359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_kind_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 2, v___x_1377_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_clearInMatchAlt___boxed(
    mut v_stx_1385_: *mut crate::leanh::LeanObject,
    mut v_vars_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_Elab_Term_clearInMatchAlt(v_stx_1385_, v_vars_1386_);
    crate::leanh::lean_dec_ref(v_vars_1386_);
    return v_res_1387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(
    mut v_vars_1388_: *mut crate::leanh::LeanObject,
    mut v_sz_1389_: usize,
    mut v_i_1390_: usize,
    mut v_bs_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: u8 = 0;
    let mut v_v_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: usize = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1392_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
                if v___x_1392_ == 0 {
                    return v_bs_1391_;
                } else {
                    v_v_1393_ = lean_array_uget(v_bs_1391_, v_i_1390_);
                    v___x_1394_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1395_ = lean_array_uset(v_bs_1391_, v_i_1390_, v___x_1394_);
                    v___x_1396_ = l_Lean_Elab_Term_clearInMatchAlt(v_v_1393_, v_vars_1388_);
                    v___x_1397_ = 1usize;
                    v___x_1398_ = lean_usize_add(v_i_1390_, v___x_1397_);
                    v___x_1399_ = lean_array_uset(v_bs_x27_1395_, v_i_1390_, v___x_1396_);
                    v_i_1390_ = v___x_1398_;
                    v_bs_1391_ = v___x_1399_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0___boxed(
    mut v_vars_1401_: *mut crate::leanh::LeanObject,
    mut v_sz_1402_: *mut crate::leanh::LeanObject,
    mut v_i_1403_: *mut crate::leanh::LeanObject,
    mut v_bs_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1405_: usize = 0;
    let mut v_i_boxed_1406_: usize = 0;
    let mut v_res_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1405_ = crate::leanh::lean_unbox_usize(v_sz_1402_);
    crate::leanh::lean_dec(v_sz_1402_);
    v_i_boxed_1406_ = crate::leanh::lean_unbox_usize(v_i_1403_);
    crate::leanh::lean_dec(v_i_1403_);
    v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_1401_, v_sz_boxed_1405_, v_i_boxed_1406_, v_bs_1404_);
    crate::leanh::lean_dec_ref(v_vars_1401_);
    return v_res_1407_;
}
pub unsafe fn l_Lean_Elab_Term_clearInMatch(
    mut v_stx_1408_: *mut crate::leanh::LeanObject,
    mut v_vars_1409_: *mut crate::leanh::LeanObject,
    mut v_a_1410_: *mut crate::leanh::LeanObject,
    mut v_a_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1468_: usize = 0;
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: usize = 0;
    let mut v_alts_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gen_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1412_ = lean_array_get_size(v_vars_1409_);
                v___x_1413_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1414_ = lean_nat_dec_eq(v___x_1412_, v___x_1413_);
                if v___x_1414_ == 0 {
                    v___x_1415_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__0;
                    v___x_1416_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__1;
                    crate::leanh::lean_inc(v_stx_1408_);
                    v___x_1481_ = l_Lean_Syntax_isOfKind(v_stx_1408_, v___x_1416_);
                    if v___x_1481_ == 0 {
                        v___x_1482_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1482_, 0, v_stx_1408_);
                        crate::leanh::lean_ctor_set(v___x_1482_, 1, v_a_1411_);
                        return v___x_1482_;
                    } else {
                        v___x_1483_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1496_ = l_Lean_Syntax_getArg(v_stx_1408_, v___x_1483_);
                        v___x_1497_ = l_Lean_Syntax_isNone(v___x_1496_);
                        if v___x_1497_ == 0 {
                            crate::leanh::lean_inc(v___x_1496_);
                            v___x_1498_ = l_Lean_Syntax_matchesNull(v___x_1496_, v___x_1483_);
                            if v___x_1498_ == 0 {
                                crate::leanh::lean_dec(v___x_1496_);
                                v___x_1499_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1499_, 0, v_stx_1408_);
                                crate::leanh::lean_ctor_set(v___x_1499_, 1, v_a_1411_);
                                return v___x_1499_;
                            } else {
                                v_gen_1500_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1413_);
                                crate::leanh::lean_dec(v___x_1496_);
                                v___x_1501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1501_, 0, v_gen_1500_);
                                v_gen_1485_ = v___x_1501_;
                                v___y_1486_ = v_a_1410_;
                                v___y_1487_ = v_a_1411_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1496_);
                            v___x_1502_ = crate::leanh::lean_box(0);
                            v_gen_1485_ = v___x_1502_;
                            v___y_1486_ = v_a_1410_;
                            v___y_1487_ = v_a_1411_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_1503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1503_, 0, v_stx_1408_);
                    crate::leanh::lean_ctor_set(v___x_1503_, 1, v_a_1411_);
                    return v___x_1503_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_1421_, 3);
                v___x_1428_ = l_Array_append___redArg(v___y_1421_, v___y_1427_);
                crate::leanh::lean_dec_ref(v___y_1427_);
                crate::leanh::lean_inc_n(v___y_1425_, 3);
                crate::leanh::lean_inc_n(v___y_1424_, 5);
                v___x_1429_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1429_, 0, v___y_1424_);
                crate::leanh::lean_ctor_set(v___x_1429_, 1, v___y_1425_);
                crate::leanh::lean_ctor_set(v___x_1429_, 2, v___x_1428_);
                v___x_1430_ = l_Array_append___redArg(v___y_1421_, v___y_1418_);
                crate::leanh::lean_dec_ref(v___y_1418_);
                v___x_1431_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1431_, 0, v___y_1424_);
                crate::leanh::lean_ctor_set(v___x_1431_, 1, v___y_1425_);
                crate::leanh::lean_ctor_set(v___x_1431_, 2, v___x_1430_);
                v___x_1432_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__2;
                v___x_1433_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1433_, 0, v___y_1424_);
                crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                v___x_1434_ = l_Array_append___redArg(v___y_1421_, v___y_1422_);
                crate::leanh::lean_dec_ref(v___y_1422_);
                v___x_1435_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1435_, 0, v___y_1424_);
                crate::leanh::lean_ctor_set(v___x_1435_, 1, v___y_1425_);
                crate::leanh::lean_ctor_set(v___x_1435_, 2, v___x_1434_);
                crate::leanh::lean_inc(v___y_1420_);
                v___x_1436_ = l_Lean_Syntax_node1(v___y_1424_, v___y_1420_, v___x_1435_);
                v___x_1437_ = l_Lean_Syntax_node6(
                    v___y_1424_,
                    v___x_1416_,
                    v___y_1426_,
                    v___y_1419_,
                    v___x_1429_,
                    v___x_1431_,
                    v___x_1433_,
                    v___x_1436_,
                );
                v___x_1438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
                crate::leanh::lean_ctor_set(v___x_1438_, 1, v___y_1423_);
                return v___x_1438_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_1443_);
                v___x_1450_ = l_Array_append___redArg(v___y_1443_, v___y_1449_);
                crate::leanh::lean_dec_ref(v___y_1449_);
                crate::leanh::lean_inc(v___y_1447_);
                crate::leanh::lean_inc(v___y_1446_);
                v___x_1451_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1451_, 0, v___y_1446_);
                crate::leanh::lean_ctor_set(v___x_1451_, 1, v___y_1447_);
                crate::leanh::lean_ctor_set(v___x_1451_, 2, v___x_1450_);
                if crate::leanh::lean_obj_tag(v___y_1441_) == 1 {
                    v_val_1452_ = crate::leanh::lean_ctor_get(v___y_1441_, 0);
                    crate::leanh::lean_inc(v_val_1452_);
                    crate::leanh::lean_dec_ref_known(v___y_1441_, 1);
                    v___x_1453_ = l_Array_mkArray1___redArg(v_val_1452_);
                    v___y_1418_ = v___y_1440_;
                    v___y_1419_ = v___x_1451_;
                    v___y_1420_ = v___y_1442_;
                    v___y_1421_ = v___y_1443_;
                    v___y_1422_ = v___y_1444_;
                    v___y_1423_ = v___y_1445_;
                    v___y_1424_ = v___y_1446_;
                    v___y_1425_ = v___y_1447_;
                    v___y_1426_ = v___y_1448_;
                    v___y_1427_ = v___x_1453_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1441_);
                    v___x_1454_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                    v___y_1418_ = v___y_1440_;
                    v___y_1419_ = v___x_1451_;
                    v___y_1420_ = v___y_1442_;
                    v___y_1421_ = v___y_1443_;
                    v___y_1422_ = v___y_1444_;
                    v___y_1423_ = v___y_1445_;
                    v___y_1424_ = v___y_1446_;
                    v___y_1425_ = v___y_1447_;
                    v___y_1426_ = v___y_1448_;
                    v___y_1427_ = v___x_1454_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1460_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_1461_ = l_Lean_Syntax_getArg(v_stx_1408_, v___x_1460_);
                v___x_1462_ = l_Lean_Elab_Term_expandMatchAlts_x3f___closed__6;
                crate::leanh::lean_inc(v___x_1461_);
                v___x_1463_ = l_Lean_Syntax_isOfKind(v___x_1461_, v___x_1462_);
                if v___x_1463_ == 0 {
                    crate::leanh::lean_dec(v___x_1461_);
                    crate::leanh::lean_dec(v_motive_1457_);
                    crate::leanh::lean_dec(v___y_1456_);
                    v___x_1464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v_stx_1408_);
                    crate::leanh::lean_ctor_set(v___x_1464_, 1, v___y_1459_);
                    return v___x_1464_;
                } else {
                    v_ref_1465_ = crate::leanh::lean_ctor_get(v___y_1458_, 5);
                    v___x_1466_ = l_Lean_Syntax_getArg(v___x_1461_, v___x_1413_);
                    crate::leanh::lean_dec(v___x_1461_);
                    v_alts_1467_ = l_Lean_Syntax_getArgs(v___x_1466_);
                    crate::leanh::lean_dec(v___x_1466_);
                    v_sz_1468_ = lean_array_size(v_alts_1467_);
                    v___x_1469_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1470_ = l_Lean_Syntax_getArg(v_stx_1408_, v___x_1469_);
                    crate::leanh::lean_dec(v_stx_1408_);
                    v___x_1471_ = l_Lean_Syntax_getArgs(v___x_1470_);
                    crate::leanh::lean_dec(v___x_1470_);
                    v___x_1472_ = 0usize;
                    v_alts_1473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_clearInMatch_spec__0(v_vars_1409_, v_sz_1468_, v___x_1472_, v_alts_1467_);
                    v___x_1474_ = l_Lean_SourceInfo_fromRef(v_ref_1465_, v___x_1414_);
                    crate::leanh::lean_inc(v___x_1474_);
                    v___x_1475_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                    crate::leanh::lean_ctor_set(v___x_1475_, 1, v___x_1415_);
                    v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_expandMatchAlt_spec__0___closed__1;
                    v___x_1477_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7_once
                        ),
                        _init_l_Lean_Elab_Term_expandMatchAlts_x3f___closed__7,
                    );
                    if crate::leanh::lean_obj_tag(v___y_1456_) == 1 {
                        v_val_1478_ = crate::leanh::lean_ctor_get(v___y_1456_, 0);
                        crate::leanh::lean_inc(v_val_1478_);
                        crate::leanh::lean_dec_ref_known(v___y_1456_, 1);
                        v___x_1479_ = l_Array_mkArray1___redArg(v_val_1478_);
                        v___y_1440_ = v___x_1471_;
                        v___y_1441_ = v_motive_1457_;
                        v___y_1442_ = v___x_1462_;
                        v___y_1443_ = v___x_1477_;
                        v___y_1444_ = v_alts_1473_;
                        v___y_1445_ = v___y_1459_;
                        v___y_1446_ = v___x_1474_;
                        v___y_1447_ = v___x_1476_;
                        v___y_1448_ = v___x_1475_;
                        v___y_1449_ = v___x_1479_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1456_);
                        v___x_1480_ = l_Lean_Elab_Term_shouldExpandMatchAlt___closed__5;
                        v___y_1440_ = v___x_1471_;
                        v___y_1441_ = v_motive_1457_;
                        v___y_1442_ = v___x_1462_;
                        v___y_1443_ = v___x_1477_;
                        v___y_1444_ = v_alts_1473_;
                        v___y_1445_ = v___y_1459_;
                        v___y_1446_ = v___x_1474_;
                        v___y_1447_ = v___x_1476_;
                        v___y_1448_ = v___x_1475_;
                        v___y_1449_ = v___x_1480_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1488_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1489_ = l_Lean_Syntax_getArg(v_stx_1408_, v___x_1488_);
                v___x_1490_ = l_Lean_Syntax_isNone(v___x_1489_);
                if v___x_1490_ == 0 {
                    crate::leanh::lean_inc(v___x_1489_);
                    v___x_1491_ = l_Lean_Syntax_matchesNull(v___x_1489_, v___x_1483_);
                    if v___x_1491_ == 0 {
                        crate::leanh::lean_dec(v___x_1489_);
                        crate::leanh::lean_dec(v_gen_1485_);
                        v___x_1492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1492_, 0, v_stx_1408_);
                        crate::leanh::lean_ctor_set(v___x_1492_, 1, v___y_1487_);
                        return v___x_1492_;
                    } else {
                        v_motive_1493_ = l_Lean_Syntax_getArg(v___x_1489_, v___x_1413_);
                        crate::leanh::lean_dec(v___x_1489_);
                        v___x_1494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1494_, 0, v_motive_1493_);
                        v___y_1456_ = v_gen_1485_;
                        v_motive_1457_ = v___x_1494_;
                        v___y_1458_ = v___y_1486_;
                        v___y_1459_ = v___y_1487_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1489_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v___y_1456_ = v_gen_1485_;
                    v_motive_1457_ = v___x_1495_;
                    v___y_1458_ = v___y_1486_;
                    v___y_1459_ = v___y_1487_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_clearInMatch___boxed(
    mut v_stx_1504_: *mut crate::leanh::LeanObject,
    mut v_vars_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Lean_Elab_Term_clearInMatch(v_stx_1504_, v_vars_1505_, v_a_1506_, v_a_1507_);
    crate::leanh::lean_dec_ref(v_a_1506_);
    crate::leanh::lean_dec_ref(v_vars_1505_);
    return v_res_1508_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BindersUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BindersUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BindersUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BindersUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BindersUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BindersUtil(builtin);
}

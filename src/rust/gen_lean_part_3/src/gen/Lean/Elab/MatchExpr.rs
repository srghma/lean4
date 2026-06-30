// Lean compiler output
// Module: Lean.Elab.MatchExpr
// Imports: Lean.Elab.Term
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwErrorAt___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node8,
    l_Lean_addMacroScope, l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Term::{
    initialize_Lean_Elab_Term, runtime_initialize_Lean_Elab_Term,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        109, 97, 116, 99, 104, 69, 120, 112, 114, 69, 108, 115, 101, 65, 108, 116, 0,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value)
            as *mut leanh::LeanObject,
        1632499211127915769 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject,3984140175429830279 as *mut leanh::LeanObject] };
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 65, 108, 116, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            4415435816164107676 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 80, 97, 116, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value)
                as *mut leanh::LeanObject,
            2538307196702464034 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_next___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Term_MatchExpr_next___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_next___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_initK___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [95, 95, 100, 111, 95, 106, 112, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_initK___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__0_value)
                as *mut leanh::LeanObject,
            15820227558662830522 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject,17201320286889277233 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 120, 112, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5816915816860015341 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5933584171502587988 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [85, 110, 105, 116, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value)
                as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 117, 112, 108, 101, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value)
            as *mut leanh::LeanObject,
        15644373471618144447 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value)
            as *mut leanh::LeanObject,
        7306243862518720553 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value)
            as *mut leanh::LeanObject,
        9871775667037945883 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [77, 97, 116, 99, 104, 69, 120, 112, 114, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value)
            as *mut leanh::LeanObject,
        3118387575542340883 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value)
            as *mut leanh::LeanObject,
        11323065835382012354 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject,5353940006376281447 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 115, 67, 111, 110, 115, 116, 79, 102, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value) as *mut leanh::LeanObject,10912452762630170651 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value) as *mut leanh::LeanObject,14296711813398647265 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 95, 100, 105, 115, 99, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value) as *mut leanh::LeanObject,16733771387975461799 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 101, 114, 109, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value) as *mut leanh::LeanObject,12532511233276993215 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value) as *mut leanh::LeanObject,13771926289831477797 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 115, 65, 112, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value) as *mut leanh::LeanObject,15267956672266940778 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value) as *mut leanh::LeanObject,146480343229376155 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value) as *mut leanh::LeanObject,17404204824591055365 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value) as *mut leanh::LeanObject,8036185514257755965 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value) as *mut leanh::LeanObject,17116161260408496210 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value) as *mut leanh::LeanObject,13708106407786339395 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 120, 112, 114, 46, 97, 112, 112, 70, 110, 67, 108, 101, 97, 110, 117, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 112, 112, 70, 110, 67, 108, 101, 97, 110, 117, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5816915816860015341 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut leanh::LeanObject,2608827092792194939 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5933584171502587988 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut leanh::LeanObject,8323309418843702446 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 112, 114, 46, 97, 112, 112, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5816915816860015341 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut leanh::LeanObject,14289070523719690127 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5933584171502587988 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut leanh::LeanObject,7686834297966724978 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 95, 100, 101, 108, 97, 121, 101, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,18341947624523515681 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__0_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__1_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__3_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        69, 120, 112, 114, 46, 99, 108, 101, 97, 110, 117, 112, 65, 110, 110, 111, 116, 97, 116,
        105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__5_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        99, 108, 101, 97, 110, 117, 112, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5816915816860015341 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value)
                as *mut leanh::LeanObject,
            8192533573043082760 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut leanh::LeanObject,5933584171502587988 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value)
                as *mut leanh::LeanObject,
            4039834411699617061 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__8_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 109, 97, 116, 99, 104, 95, 101,
        120, 112, 114, 96, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 0,
    ],
};
static mut l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_main___closed__0_value: leanh::LeanStringObject<41> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 109, 97, 116, 99, 104, 95,
            101, 120, 112, 114, 96, 32, 101, 108, 115, 101, 45, 97, 108, 116, 101, 114, 110, 97,
            116, 105, 118, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_main___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_main___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandMatchExpr___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Term_expandMatchExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_expandMatchExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__0_value)
                as *mut leanh::LeanObject,
            6386943139076865352 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandMatchExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 120, 112, 97, 110, 100, 77, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,7892421401833366012 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value) as *mut leanh::LeanObject,17839991279989882916 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 207 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [108, 101, 116, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_expandLetExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__0_value)
                as *mut leanh::LeanObject,
            9932332765764045546 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__2_value: leanh::LeanStringObject<11> =
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
        m_data: [109, 97, 116, 99, 104, 95, 101, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__3_value: leanh::LeanStringObject<5> =
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
        m_data: [119, 105, 116, 104, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__4_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            109, 97, 116, 99, 104, 69, 120, 112, 114, 65, 108, 116, 115, 0,
        ],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_expandLetExpr___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__4_value)
                as *mut leanh::LeanObject,
            13500049350435642968 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__6_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [124, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__7_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_expandLetExpr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 112, 97, 110, 100, 76, 101, 116, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut leanh::LeanObject,7892421401833366012 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value) as *mut leanh::LeanObject,6927429308684558226 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 215 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 59 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 59 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(
    mut v_stx_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    v___x_1705_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4;
    leanh::lean_inc(v_stx_1704_);
    v___x_1706_ = l_Lean_Syntax_isOfKind(v_stx_1704_, v___x_1705_);
    if v___x_1706_ == 0 {
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1704_);
        v___x_1707_ = leanh::lean_box(0);
        return v___x_1707_;
    } else {
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1708_ = leanh::lean_unsigned_to_nat(3);
        v___x_1709_ = l_Lean_Syntax_getArg(v_stx_1704_, v___x_1708_);
        leanh::lean_dec(v_stx_1704_);
        v___x_1710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1710_, 0, v___x_1709_);
        return v___x_1710_;
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1717_) == 0 {
                    v___x_1719_ = l_List_reverse___redArg(v_a_1718_);
                    return v___x_1719_;
                } else {
                    v_head_1720_ = leanh::lean_ctor_get(v_a_1717_, 0);
                    v_tail_1721_ = leanh::lean_ctor_get(v_a_1717_, 1);
                    v_isSharedCheck_1735_ = (!leanh::lean_is_exclusive(v_a_1717_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1723_ = v_a_1717_;
                        v_isShared_1724_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1721_);
                        leanh::lean_inc(v_head_1720_);
                        leanh::lean_dec(v_a_1717_);
                        v___x_1723_ = leanh::lean_box(0);
                        v_isShared_1724_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1731_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                leanh::lean_inc(v_head_1720_);
                v___x_1732_ = l_Lean_Syntax_isOfKind(v_head_1720_, v___x_1731_);
                if v___x_1732_ == 0 {
                    v___x_1733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1733_, 0, v_head_1720_);
                    v___y_1726_ = v___x_1733_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_head_1720_);
                    v___x_1734_ = leanh::lean_box(0);
                    v___y_1726_ = v___x_1734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1724_ == 0 {
                    leanh::lean_ctor_set(v___x_1723_, 1, v_a_1718_);
                    leanh::lean_ctor_set(v___x_1723_, 0, v___y_1726_);
                    v___x_1728_ = v___x_1723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___y_1726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1718_);
                    v___x_1728_ = v_reuseFailAlloc_1730_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1717_ = v_tail_1721_;
                v_a_1718_ = v___x_1728_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_toAlt_x3f(
    mut v_stx_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1752_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1;
                leanh::lean_inc(v_stx_1751_);
                v___x_1753_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1752_);
                if v___x_1753_ == 0 {
                    leanh::lean_dec(v_stx_1751_);
                    v___x_1754_ = leanh::lean_box(0);
                    return v___x_1754_;
                } else {
                    v___x_1755_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1756_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1755_);
                    v___x_1775_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5;
                    leanh::lean_inc(v___x_1756_);
                    v___x_1776_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1775_);
                    if v___x_1776_ == 0 {
                        leanh::lean_dec(v___x_1756_);
                        leanh::lean_dec(v_stx_1751_);
                        v___x_1777_ = leanh::lean_box(0);
                        return v___x_1777_;
                    } else {
                        v___x_1778_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1779_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1778_);
                        v___x_1780_ = l_Lean_Syntax_isNone(v___x_1779_);
                        if v___x_1780_ == 0 {
                            v___x_1781_ = leanh::lean_unsigned_to_nat(2);
                            leanh::lean_inc(v___x_1779_);
                            v___x_1782_ = l_Lean_Syntax_matchesNull(v___x_1779_, v___x_1781_);
                            if v___x_1782_ == 0 {
                                leanh::lean_dec(v___x_1779_);
                                leanh::lean_dec(v___x_1756_);
                                leanh::lean_dec(v_stx_1751_);
                                v___x_1783_ = leanh::lean_box(0);
                                return v___x_1783_;
                            } else {
                                v_var_x3f_1784_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1778_);
                                leanh::lean_dec(v___x_1779_);
                                v___x_1785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1785_, 0, v_var_x3f_1784_);
                                v_var_x3f_1758_ = v___x_1785_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1779_);
                            v___x_1786_ = leanh::lean_box(0);
                            v_var_x3f_1758_ = v___x_1786_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_funName_1759_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1755_);
                v___x_1760_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3;
                leanh::lean_inc(v_funName_1759_);
                v___x_1761_ = l_Lean_Syntax_isOfKind(v_funName_1759_, v___x_1760_);
                if v___x_1761_ == 0 {
                    leanh::lean_dec(v_funName_1759_);
                    leanh::lean_dec(v_var_x3f_1758_);
                    leanh::lean_dec(v___x_1756_);
                    leanh::lean_dec(v_stx_1751_);
                    v___x_1762_ = leanh::lean_box(0);
                    return v___x_1762_;
                } else {
                    v___x_1763_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1764_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1763_);
                    leanh::lean_dec(v___x_1756_);
                    v_pvars_1765_ = l_Lean_Syntax_getArgs(v___x_1764_);
                    leanh::lean_dec(v___x_1764_);
                    v___x_1766_ = lean_array_to_list(v_pvars_1765_);
                    v___x_1767_ = l_List_reverse___redArg(v___x_1766_);
                    v___x_1768_ = leanh::lean_box(0);
                    v_pvars_1769_ =
                        l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(
                            v___x_1767_,
                            v___x_1768_,
                        );
                    v___x_1770_ = leanh::lean_unsigned_to_nat(3);
                    v_rhs_1771_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1770_);
                    leanh::lean_dec(v_stx_1751_);
                    v___x_1772_ = leanh::lean_box(0);
                    v___x_1773_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v___x_1773_, 0, v_var_x3f_1758_);
                    leanh::lean_ctor_set(v___x_1773_, 1, v_funName_1759_);
                    leanh::lean_ctor_set(v___x_1773_, 2, v_pvars_1769_);
                    leanh::lean_ctor_set(v___x_1773_, 3, v_rhs_1771_);
                    leanh::lean_ctor_set(v___x_1773_, 4, v___x_1772_);
                    leanh::lean_ctor_set(v___x_1773_, 5, v___x_1768_);
                    v___x_1774_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1774_, 0, v___x_1773_);
                    return v___x_1774_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(
    mut v_a_1790_: *mut leanh::LeanObject,
    mut v_as_1791_: *mut leanh::LeanObject,
    mut v_sz_1792_: usize,
    mut v_i_1793_: usize,
    mut v_b_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1795_: u8 = 0;
    let mut v_funName_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: usize = 0;
    let mut v___x_1804_: usize = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_usize_dec_lt(v_i_1793_, v_sz_1792_);
                if v___x_1795_ == 0 {
                    leanh::lean_inc_ref(v_b_1794_);
                    return v_b_1794_;
                } else {
                    v_funName_1796_ = leanh::lean_ctor_get(v_a_1790_, 1);
                    v___x_1797_ = leanh::lean_box(0);
                    v_a_1798_ = lean_array_uget_borrowed(v_as_1791_, v_i_1793_);
                    v___x_1799_ = l_Lean_TSyntax_getId(v_a_1798_);
                    v___x_1800_ = l_Lean_TSyntax_getId(v_funName_1796_);
                    v___x_1801_ = lean_name_eq(v___x_1799_, v___x_1800_);
                    leanh::lean_dec(v___x_1800_);
                    leanh::lean_dec(v___x_1799_);
                    if v___x_1801_ == 0 {
                        v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0;
                        v___x_1803_ = 1usize;
                        v___x_1804_ = lean_usize_add(v_i_1793_, v___x_1803_);
                        v_i_1793_ = v___x_1804_;
                        v_b_1794_ = v___x_1802_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1798_);
                        v___x_1806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1806_, 0, v_a_1798_);
                        v___x_1807_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                        v___x_1808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1808_, 0, v___x_1807_);
                        leanh::lean_ctor_set(v___x_1808_, 1, v___x_1797_);
                        return v___x_1808_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(
    mut v_a_1809_: *mut leanh::LeanObject,
    mut v_as_1810_: *mut leanh::LeanObject,
    mut v_sz_1811_: *mut leanh::LeanObject,
    mut v_i_1812_: *mut leanh::LeanObject,
    mut v_b_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1814_: usize = 0;
    let mut v_i_boxed_1815_: usize = 0;
    let mut v_res_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1814_ = leanh::lean_unbox_usize(v_sz_1811_);
    leanh::lean_dec(v_sz_1811_);
    v_i_boxed_1815_ = leanh::lean_unbox_usize(v_i_1812_);
    leanh::lean_dec(v_i_1812_);
    v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_1809_, v_as_1810_, v_sz_boxed_1814_, v_i_boxed_1815_, v_b_1813_);
    leanh::lean_dec_ref(v_b_1813_);
    leanh::lean_dec_ref(v_as_1810_);
    leanh::lean_dec_ref(v_a_1809_);
    return v_res_1816_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
    mut v_as_x27_1817_: *mut leanh::LeanObject,
    mut v_b_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1830_: usize = 0;
    let mut v___x_1831_: usize = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_1817_) == 0 {
                    return v_b_1818_;
                } else {
                    v_head_1819_ = leanh::lean_ctor_get(v_as_x27_1817_, 0);
                    v_tail_1820_ = leanh::lean_ctor_get(v_as_x27_1817_, 1);
                    v_funName_1821_ = leanh::lean_ctor_get(v_head_1819_, 1);
                    v_pvars_1822_ = leanh::lean_ctor_get(v_head_1819_, 2);
                    v___x_1823_ = l_List_isEmpty___redArg(v_pvars_1822_);
                    if v___x_1823_ == 0 {
                        v_as_x27_1817_ = v_tail_1820_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0;
                        v_sz_1830_ = lean_array_size(v_b_1818_);
                        v___x_1831_ = 0usize;
                        v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_head_1819_, v_b_1818_, v_sz_1830_, v___x_1831_, v___x_1829_);
                        v_fst_1833_ = leanh::lean_ctor_get(v___x_1832_, 0);
                        leanh::lean_inc(v_fst_1833_);
                        leanh::lean_dec_ref(v___x_1832_);
                        if leanh::lean_obj_tag(v_fst_1833_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_val_1834_ = leanh::lean_ctor_get(v_fst_1833_, 0);
                            leanh::lean_inc(v_val_1834_);
                            leanh::lean_dec_ref_known(v_fst_1833_, 1);
                            if leanh::lean_obj_tag(v_val_1834_) == 0 {
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_val_1834_, 1);
                                v_as_x27_1817_ = v_tail_1820_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___x_1823_ == 0 {
                    v_as_x27_1817_ = v_tail_1820_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_funName_1821_);
                    v___x_1826_ = lean_array_push(v_b_1818_, v_funName_1821_);
                    v_as_x27_1817_ = v_tail_1820_;
                    v_b_1818_ = v___x_1826_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg___boxed(
    mut v_as_x27_1836_: *mut leanh::LeanObject,
    mut v_b_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
            v_as_x27_1836_,
            v_b_1837_,
        );
    leanh::lean_dec(v_as_x27_1836_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(
    mut v_alts_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_funNames_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_funNames_1842_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
    v___x_1843_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
            v_alts_1841_,
            v_funNames_1842_,
        );
    v___x_1844_ = lean_array_to_list(v___x_1843_);
    return v___x_1844_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___boxed(
    mut v_alts_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_1845_);
    leanh::lean_dec(v_alts_1845_);
    return v_res_1846_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(
    mut v_as_1847_: *mut leanh::LeanObject,
    mut v_as_x27_1848_: *mut leanh::LeanObject,
    mut v_b_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
            v_as_x27_1848_,
            v_b_1849_,
        );
    return v___x_1851_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(
    mut v_as_1852_: *mut leanh::LeanObject,
    mut v_as_x27_1853_: *mut leanh::LeanObject,
    mut v_b_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(
            v_as_1852_,
            v_as_x27_1853_,
            v_b_1854_,
            v_a_1855_,
        );
    leanh::lean_dec(v_as_x27_1853_);
    leanh::lean_dec(v_as_1852_);
    return v_res_1856_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(
    mut v_x_1857_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1858_: u8 = 0;
    let mut v_head_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: u8 = 0;
    let mut v_tail_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1857_) == 0 {
                    v___x_1858_ = 0;
                    return v___x_1858_;
                } else {
                    v_head_1859_ = leanh::lean_ctor_get(v_x_1857_, 0);
                    v_pvars_1860_ = leanh::lean_ctor_get(v_head_1859_, 2);
                    if leanh::lean_obj_tag(v_pvars_1860_) == 1 {
                        v_head_1861_ = leanh::lean_ctor_get(v_pvars_1860_, 0);
                        if leanh::lean_obj_tag(v_head_1861_) == 1 {
                            v___x_1862_ = 1;
                            return v___x_1862_;
                        } else {
                            v_tail_1863_ = leanh::lean_ctor_get(v_x_1857_, 1);
                            v_x_1857_ = v_tail_1863_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_1865_ = leanh::lean_ctor_get(v_x_1857_, 1);
                        v_x_1857_ = v_tail_1865_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0___boxed(
    mut v_x_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1868_: u8 = 0;
    let mut v_r_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_x_1867_);
    leanh::lean_dec(v_x_1867_);
    v_r_1869_ = leanh::lean_box((v_res_1868_) as usize);
    return v_r_1869_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_shouldSaveActual(
    mut v_alts_1870_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1871_: u8 = 0;
    v___x_1871_ =
        l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(
    mut v_alts_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1873_: u8 = 0;
    let mut v_r_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_1872_);
    leanh::lean_dec(v_alts_1872_);
    v_r_1874_ = leanh::lean_box((v_res_1873_) as usize);
    return v_r_1874_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
    mut v_funName_1875_: *mut leanh::LeanObject,
    mut v_x_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: u8 = 0;
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u8 = 0;
    let mut v___x_1889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1876_) == 0 {
                    v___x_1877_ = leanh::lean_box(0);
                    return v___x_1877_;
                } else {
                    v_head_1878_ = leanh::lean_ctor_get(v_x_1876_, 0);
                    v_tail_1879_ = leanh::lean_ctor_get(v_x_1876_, 1);
                    v_funName_1884_ = leanh::lean_ctor_get(v_head_1878_, 1);
                    v_pvars_1885_ = leanh::lean_ctor_get(v_head_1878_, 2);
                    v___x_1886_ = l_Lean_TSyntax_getId(v_funName_1884_);
                    v___x_1887_ = l_Lean_TSyntax_getId(v_funName_1875_);
                    v___x_1888_ = lean_name_eq(v___x_1886_, v___x_1887_);
                    leanh::lean_dec(v___x_1887_);
                    leanh::lean_dec(v___x_1886_);
                    if v___x_1888_ == 0 {
                        v___y_1881_ = v___x_1888_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1889_ = l_List_isEmpty___redArg(v_pvars_1885_);
                        v___y_1881_ = v___x_1889_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1881_ == 0 {
                    v_x_1876_ = v_tail_1879_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_head_1878_);
                    v___x_1883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1883_, 0, v_head_1878_);
                    return v___x_1883_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0___boxed(
    mut v_funName_1890_: *mut leanh::LeanObject,
    mut v_x_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
        v_funName_1890_,
        v_x_1891_,
    );
    leanh::lean_dec(v_x_1891_);
    leanh::lean_dec(v_funName_1890_);
    return v_res_1892_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(
    mut v_alts_1893_: *mut leanh::LeanObject,
    mut v_funName_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1895_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
        v_funName_1894_,
        v_alts_1893_,
    );
    return v___x_1895_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___boxed(
    mut v_alts_1896_: *mut leanh::LeanObject,
    mut v_funName_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(v_alts_1896_, v_funName_1897_);
    leanh::lean_dec(v_funName_1897_);
    leanh::lean_dec(v_alts_1896_);
    return v_res_1898_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(
    mut v_actual_1899_: *mut leanh::LeanObject,
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v_head_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_unused_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1900_) == 0 {
                    leanh::lean_dec(v_actual_1899_);
                    v___x_1902_ = lean_array_to_list(v_a_1901_);
                    return v___x_1902_;
                } else {
                    v_head_1903_ = leanh::lean_ctor_get(v_a_1900_, 0);
                    leanh::lean_inc(v_head_1903_);
                    v_tail_1904_ = leanh::lean_ctor_get(v_a_1900_, 1);
                    leanh::lean_inc(v_tail_1904_);
                    leanh::lean_dec_ref_known(v_a_1900_, 2);
                    v_var_x3f_1909_ = leanh::lean_ctor_get(v_head_1903_, 0);
                    v_funName_1910_ = leanh::lean_ctor_get(v_head_1903_, 1);
                    v_pvars_1911_ = leanh::lean_ctor_get(v_head_1903_, 2);
                    v_rhs_1912_ = leanh::lean_ctor_get(v_head_1903_, 3);
                    v_k_1913_ = leanh::lean_ctor_get(v_head_1903_, 4);
                    v_actuals_1914_ = leanh::lean_ctor_get(v_head_1903_, 5);
                    v_isSharedCheck_1937_ = (!leanh::lean_is_exclusive(v_head_1903_)) as u8;
                    if v_isSharedCheck_1937_ == 0 {
                        v___x_1916_ = v_head_1903_;
                        v_isShared_1917_ = v_isSharedCheck_1937_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_actuals_1914_);
                        leanh::lean_inc(v_k_1913_);
                        leanh::lean_inc(v_rhs_1912_);
                        leanh::lean_inc(v_pvars_1911_);
                        leanh::lean_inc(v_funName_1910_);
                        leanh::lean_inc(v_var_x3f_1909_);
                        leanh::lean_dec(v_head_1903_);
                        v___x_1916_ = leanh::lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_1937_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1907_ = lean_array_push(v_a_1901_, v_val_1906_);
                v_a_1900_ = v_tail_1904_;
                v_a_1901_ = v___x_1907_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v_pvars_1911_) == 1 {
                    v_head_1926_ = leanh::lean_ctor_get(v_pvars_1911_, 0);
                    if leanh::lean_obj_tag(v_head_1926_) == 1 {
                        leanh::lean_del_object(v___x_1916_);
                        v_tail_1927_ = leanh::lean_ctor_get(v_pvars_1911_, 1);
                        v_isSharedCheck_1935_ =
                            (!leanh::lean_is_exclusive(v_pvars_1911_)) as u8;
                        if v_isSharedCheck_1935_ == 0 {
                            v_unused_1936_ = leanh::lean_ctor_get(v_pvars_1911_, 0);
                            leanh::lean_dec(v_unused_1936_);
                            v___x_1929_ = v_pvars_1911_;
                            v_isShared_1930_ = v_isSharedCheck_1935_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_1927_);
                            leanh::lean_dec(v_pvars_1911_);
                            v___x_1929_ = leanh::lean_box(0);
                            v_isShared_1930_ = v_isSharedCheck_1935_;
                            state = 5;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_pvars_1911_) == 1 {
                    v_head_1919_ = leanh::lean_ctor_get(v_pvars_1911_, 0);
                    if leanh::lean_obj_tag(v_head_1919_) == 0 {
                        v_tail_1920_ = leanh::lean_ctor_get(v_pvars_1911_, 1);
                        leanh::lean_inc(v_tail_1920_);
                        leanh::lean_dec_ref_known(v_pvars_1911_, 2);
                        if v_isShared_1917_ == 0 {
                            leanh::lean_ctor_set(v___x_1916_, 2, v_tail_1920_);
                            v___x_1922_ = v___x_1916_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1923_ =
                                leanh::lean_alloc_ctor(0, 6, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_var_x3f_1909_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_funName_1910_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_tail_1920_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_rhs_1912_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_k_1913_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_actuals_1914_);
                            v___x_1922_ = v_reuseFailAlloc_1923_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_pvars_1911_, 2);
                        leanh::lean_del_object(v___x_1916_);
                        leanh::lean_dec(v_actuals_1914_);
                        leanh::lean_dec(v_k_1913_);
                        leanh::lean_dec(v_rhs_1912_);
                        leanh::lean_dec(v_funName_1910_);
                        leanh::lean_dec(v_var_x3f_1909_);
                        v_a_1900_ = v_tail_1904_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1916_);
                    leanh::lean_dec(v_actuals_1914_);
                    leanh::lean_dec(v_k_1913_);
                    leanh::lean_dec(v_rhs_1912_);
                    leanh::lean_dec(v_pvars_1911_);
                    leanh::lean_dec(v_funName_1910_);
                    leanh::lean_dec(v_var_x3f_1909_);
                    v_a_1900_ = v_tail_1904_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                v_val_1906_ = v___x_1922_;
                state = 1;
                continue;
            }
            5 => {
                leanh::lean_inc(v_actual_1899_);
                if v_isShared_1930_ == 0 {
                    leanh::lean_ctor_set(v___x_1929_, 1, v_actuals_1914_);
                    leanh::lean_ctor_set(v___x_1929_, 0, v_actual_1899_);
                    v___x_1932_ = v___x_1929_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_actual_1899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_actuals_1914_);
                    v___x_1932_ = v_reuseFailAlloc_1934_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1933_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_1933_, 0, v_var_x3f_1909_);
                leanh::lean_ctor_set(v___x_1933_, 1, v_funName_1910_);
                leanh::lean_ctor_set(v___x_1933_, 2, v_tail_1927_);
                leanh::lean_ctor_set(v___x_1933_, 3, v_rhs_1912_);
                leanh::lean_ctor_set(v___x_1933_, 4, v_k_1913_);
                leanh::lean_ctor_set(v___x_1933_, 5, v___x_1932_);
                v_val_1906_ = v___x_1933_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_next(
    mut v_alts_1940_: *mut leanh::LeanObject,
    mut v_actual_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_Elab_Term_MatchExpr_next___closed__0;
    v___x_1943_ = l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(
        v_actual_1941_,
        v_alts_1940_,
        v___x_1942_,
    );
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_Elab_Term_MatchExpr_initK___closed__0;
    v___x_1946_ = l_String_toRawSubstring_x27(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_initK(
    mut v_alt_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_macroScope_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1957_: u8 = 0;
    let mut v_quotContext_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funName_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_1952_ = leanh::lean_ctor_get(v_a_1951_, 0);
                v_traceMsgs_1953_ = leanh::lean_ctor_get(v_a_1951_, 1);
                v_expandedMacroDecls_1954_ = leanh::lean_ctor_get(v_a_1951_, 2);
                v_isSharedCheck_1986_ = (!leanh::lean_is_exclusive(v_a_1951_)) as u8;
                if v_isSharedCheck_1986_ == 0 {
                    v___x_1956_ = v_a_1951_;
                    v_isShared_1957_ = v_isSharedCheck_1986_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expandedMacroDecls_1954_);
                    leanh::lean_inc(v_traceMsgs_1953_);
                    leanh::lean_inc(v_macroScope_1952_);
                    leanh::lean_dec(v_a_1951_);
                    v___x_1956_ = leanh::lean_box(0);
                    v_isShared_1957_ = v_isSharedCheck_1986_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_1958_ = leanh::lean_ctor_get(v_a_1950_, 1);
                v_ref_1959_ = leanh::lean_ctor_get(v_a_1950_, 5);
                v_var_x3f_1960_ = leanh::lean_ctor_get(v_alt_1949_, 0);
                v_funName_1961_ = leanh::lean_ctor_get(v_alt_1949_, 1);
                v_pvars_1962_ = leanh::lean_ctor_get(v_alt_1949_, 2);
                v_rhs_1963_ = leanh::lean_ctor_get(v_alt_1949_, 3);
                v_actuals_1964_ = leanh::lean_ctor_get(v_alt_1949_, 5);
                v_isSharedCheck_1984_ = (!leanh::lean_is_exclusive(v_alt_1949_)) as u8;
                if v_isSharedCheck_1984_ == 0 {
                    v_unused_1985_ = leanh::lean_ctor_get(v_alt_1949_, 4);
                    leanh::lean_dec(v_unused_1985_);
                    v___x_1966_ = v_alt_1949_;
                    v_isShared_1967_ = v_isSharedCheck_1984_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_actuals_1964_);
                    leanh::lean_inc(v_rhs_1963_);
                    leanh::lean_inc(v_pvars_1962_);
                    leanh::lean_inc(v_funName_1961_);
                    leanh::lean_inc(v_var_x3f_1960_);
                    leanh::lean_dec(v_alt_1949_);
                    v___x_1966_ = leanh::lean_box(0);
                    v_isShared_1967_ = v_isSharedCheck_1984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1968_ = leanh::lean_unsigned_to_nat(1);
                v___x_1969_ = lean_nat_add(v_macroScope_1952_, v___x_1968_);
                v___x_1970_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1_once),
                    _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1,
                );
                if v_isShared_1957_ == 0 {
                    leanh::lean_ctor_set(v___x_1956_, 0, v___x_1969_);
                    v___x_1972_ = v___x_1956_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1983_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_traceMsgs_1953_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1983_,
                        2,
                        v_expandedMacroDecls_1954_,
                    );
                    v___x_1972_ = v_reuseFailAlloc_1983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1973_ = 0;
                v___x_1974_ = l_Lean_SourceInfo_fromRef(v_ref_1959_, v___x_1973_);
                v___x_1975_ = l_Lean_Elab_Term_MatchExpr_initK___closed__2;
                leanh::lean_inc(v_quotContext_1958_);
                v___x_1976_ =
                    l_Lean_addMacroScope(v_quotContext_1958_, v___x_1975_, v_macroScope_1952_);
                v___x_1977_ = leanh::lean_box(0);
                v___x_1978_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1978_, 0, v___x_1974_);
                leanh::lean_ctor_set(v___x_1978_, 1, v___x_1970_);
                leanh::lean_ctor_set(v___x_1978_, 2, v___x_1976_);
                leanh::lean_ctor_set(v___x_1978_, 3, v___x_1977_);
                if v_isShared_1967_ == 0 {
                    leanh::lean_ctor_set(v___x_1966_, 4, v___x_1978_);
                    v___x_1980_ = v___x_1966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_var_x3f_1960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_funName_1961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_pvars_1962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_rhs_1963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 4, v___x_1978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 5, v_actuals_1964_);
                    v___x_1980_ = v_reuseFailAlloc_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1981_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1981_, 0, v___x_1980_);
                leanh::lean_ctor_set(v___x_1981_, 1, v___x_1972_);
                return v___x_1981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_initK___boxed(
    mut v_alt_1987_: *mut leanh::LeanObject,
    mut v_a_1988_: *mut leanh::LeanObject,
    mut v_a_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1990_ = l_Lean_Elab_Term_MatchExpr_initK(v_alt_1987_, v_a_1988_, v_a_1989_);
    leanh::lean_dec_ref(v_a_1988_);
    return v_res_1990_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(
    mut v_sz_1991_: usize,
    mut v_i_1992_: usize,
    mut v_bs_1993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: u8 = 0;
    let mut v_v_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: usize = 0;
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1994_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
                if v___x_1994_ == 0 {
                    return v_bs_1993_;
                } else {
                    v_v_1995_ = lean_array_uget(v_bs_1993_, v_i_1992_);
                    v___x_1996_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1997_ = lean_array_uset(v_bs_1993_, v_i_1992_, v___x_1996_);
                    v___x_1998_ = 1usize;
                    v___x_1999_ = lean_usize_add(v_i_1992_, v___x_1998_);
                    v___x_2000_ = lean_array_uset(v_bs_x27_1997_, v_i_1992_, v_v_1995_);
                    v_i_1992_ = v___x_1999_;
                    v_bs_1993_ = v___x_2000_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1___boxed(
    mut v_sz_2002_: *mut leanh::LeanObject,
    mut v_i_2003_: *mut leanh::LeanObject,
    mut v_bs_2004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2005_: usize = 0;
    let mut v_i_boxed_2006_: usize = 0;
    let mut v_res_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2005_ = leanh::lean_unbox_usize(v_sz_2002_);
    leanh::lean_dec(v_sz_2002_);
    v_i_boxed_2006_ = leanh::lean_unbox_usize(v_i_2003_);
    leanh::lean_dec(v_i_2003_);
    v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_boxed_2005_, v_i_boxed_2006_, v_bs_2004_);
    return v_res_2007_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6;
    v___x_2021_ = l_String_toRawSubstring_x27(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2038_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2038_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(
    mut v_as_2040_: *mut leanh::LeanObject,
    mut v_i_2041_: usize,
    mut v_stop_2042_: usize,
    mut v_b_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: usize = 0;
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_usize_dec_eq(v_i_2041_, v_stop_2042_);
                if v___x_2052_ == 0 {
                    v___x_2053_ = lean_array_uget_borrowed(v_as_2040_, v_i_2041_);
                    if leanh::lean_obj_tag(v___x_2053_) == 0 {
                        v_a_2047_ = v_b_2043_;
                        v_a_2048_ = v___y_2045_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2054_ = leanh::lean_ctor_get(v___x_2053_, 0);
                        v_quotContext_2055_ = leanh::lean_ctor_get(v___y_2044_, 1);
                        v_currMacroScope_2056_ = leanh::lean_ctor_get(v___y_2044_, 2);
                        v_ref_2057_ = leanh::lean_ctor_get(v___y_2044_, 5);
                        v___x_2058_ = l_Lean_SourceInfo_fromRef(v_ref_2057_, v___x_2052_);
                        v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                        v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                        leanh::lean_inc_n(v___x_2058_, 7);
                        v___x_2061_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2061_, 0, v___x_2058_);
                        leanh::lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                        v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                        leanh::lean_inc(v_val_2054_);
                        v___x_2063_ = l_Lean_Syntax_node1(v___x_2058_, v___x_2062_, v_val_2054_);
                        v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                        v___x_2065_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2065_, 0, v___x_2058_);
                        leanh::lean_ctor_set(v___x_2065_, 1, v___x_2064_);
                        v___x_2066_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
                        v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8;
                        leanh::lean_inc(v_currMacroScope_2056_);
                        leanh::lean_inc(v_quotContext_2055_);
                        v___x_2068_ = l_Lean_addMacroScope(
                            v_quotContext_2055_,
                            v___x_2067_,
                            v_currMacroScope_2056_,
                        );
                        v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13;
                        v___x_2070_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_2070_, 0, v___x_2058_);
                        leanh::lean_ctor_set(v___x_2070_, 1, v___x_2066_);
                        leanh::lean_ctor_set(v___x_2070_, 2, v___x_2068_);
                        leanh::lean_ctor_set(v___x_2070_, 3, v___x_2069_);
                        v___x_2071_ =
                            l_Lean_Syntax_node2(v___x_2058_, v___x_2062_, v___x_2065_, v___x_2070_);
                        v___x_2072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                        v___x_2073_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2073_, 0, v___x_2058_);
                        leanh::lean_ctor_set(v___x_2073_, 1, v___x_2062_);
                        leanh::lean_ctor_set(v___x_2073_, 2, v___x_2072_);
                        v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                        v___x_2075_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2075_, 0, v___x_2058_);
                        leanh::lean_ctor_set(v___x_2075_, 1, v___x_2074_);
                        v___x_2076_ = l_Lean_Syntax_node5(
                            v___x_2058_,
                            v___x_2059_,
                            v___x_2061_,
                            v___x_2063_,
                            v___x_2071_,
                            v___x_2073_,
                            v___x_2075_,
                        );
                        v___x_2077_ = lean_array_push(v_b_2043_, v___x_2076_);
                        v_a_2047_ = v___x_2077_;
                        v_a_2048_ = v___y_2045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2078_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2078_, 0, v_b_2043_);
                    leanh::lean_ctor_set(v___x_2078_, 1, v___y_2045_);
                    return v___x_2078_;
                }
            }
            1 => {
                v___x_2049_ = 1usize;
                v___x_2050_ = lean_usize_add(v_i_2041_, v___x_2049_);
                v_i_2041_ = v___x_2050_;
                v_b_2043_ = v_a_2047_;
                v___y_2045_ = v_a_2048_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___boxed(
    mut v_as_2079_: *mut leanh::LeanObject,
    mut v_i_2080_: *mut leanh::LeanObject,
    mut v_stop_2081_: *mut leanh::LeanObject,
    mut v_b_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2085_: usize = 0;
    let mut v_stop_boxed_2086_: usize = 0;
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2085_ = leanh::lean_unbox_usize(v_i_2080_);
    leanh::lean_dec(v_i_2080_);
    v_stop_boxed_2086_ = leanh::lean_unbox_usize(v_stop_2081_);
    leanh::lean_dec(v_stop_2081_);
    v_res_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2079_, v_i_boxed_2085_, v_stop_boxed_2086_, v_b_2082_, v___y_2083_, v___y_2084_);
    leanh::lean_dec_ref(v___y_2083_);
    leanh::lean_dec_ref(v_as_2079_);
    return v_res_2087_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
    mut v_as_2088_: *mut leanh::LeanObject,
    mut v_start_2089_: *mut leanh::LeanObject,
    mut v_stop_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    v___x_2093_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
    v___x_2094_ = lean_nat_dec_lt(v_start_2089_, v_stop_2090_);
    if v___x_2094_ == 0 {
        let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2095_, 0, v___x_2093_);
        leanh::lean_ctor_set(v___x_2095_, 1, v___y_2092_);
        return v___x_2095_;
    } else {
        let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: u8 = 0;
        v___x_2096_ = lean_array_get_size(v_as_2088_);
        v___x_2097_ = lean_nat_dec_le(v_stop_2090_, v___x_2096_);
        if v___x_2097_ == 0 {
            let mut v___x_2098_: u8 = 0;
            v___x_2098_ = lean_nat_dec_lt(v_start_2089_, v___x_2096_);
            if v___x_2098_ == 0 {
                let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2099_, 0, v___x_2093_);
                leanh::lean_ctor_set(v___x_2099_, 1, v___y_2092_);
                return v___x_2099_;
            } else {
                let mut v___x_2100_: usize = 0;
                let mut v___x_2101_: usize = 0;
                let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2100_ = lean_usize_of_nat(v_start_2089_);
                v___x_2101_ = lean_usize_of_nat(v___x_2096_);
                v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2088_, v___x_2100_, v___x_2101_, v___x_2093_, v___y_2091_, v___y_2092_);
                return v___x_2102_;
            }
        } else {
            let mut v___x_2103_: usize = 0;
            let mut v___x_2104_: usize = 0;
            let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2103_ = lean_usize_of_nat(v_start_2089_);
            v___x_2104_ = lean_usize_of_nat(v_stop_2090_);
            v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2088_, v___x_2103_, v___x_2104_, v___x_2093_, v___y_2091_, v___y_2092_);
            return v___x_2105_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(
    mut v_as_2106_: *mut leanh::LeanObject,
    mut v_start_2107_: *mut leanh::LeanObject,
    mut v_stop_2108_: *mut leanh::LeanObject,
    mut v___y_2109_: *mut leanh::LeanObject,
    mut v___y_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2111_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
        v_as_2106_,
        v_start_2107_,
        v_stop_2108_,
        v___y_2109_,
        v___y_2110_,
    );
    leanh::lean_dec_ref(v___y_2109_);
    leanh::lean_dec(v_stop_2108_);
    leanh::lean_dec(v_start_2107_);
    leanh::lean_dec_ref(v_as_2106_);
    return v_res_2111_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__1;
    v___x_2115_ = l_String_toRawSubstring_x27(v___x_2114_);
    return v___x_2115_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getParams(
    mut v_alt_2129_: *mut leanh::LeanObject,
    mut v_a_2130_: *mut leanh::LeanObject,
    mut v_a_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_var_x3f_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pvars_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v_sz_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
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
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_params_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
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
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_var_x3f_2132_ = leanh::lean_ctor_get(v_alt_2129_, 0);
                leanh::lean_inc(v_var_x3f_2132_);
                v_pvars_2133_ = leanh::lean_ctor_get(v_alt_2129_, 2);
                leanh::lean_inc(v_pvars_2133_);
                leanh::lean_dec_ref(v_alt_2129_);
                v_params_2191_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
                if leanh::lean_obj_tag(v_var_x3f_2132_) == 1 {
                    v_val_2192_ = leanh::lean_ctor_get(v_var_x3f_2132_, 0);
                    leanh::lean_inc(v_val_2192_);
                    leanh::lean_dec_ref_known(v_var_x3f_2132_, 1);
                    v_quotContext_2193_ = leanh::lean_ctor_get(v_a_2130_, 1);
                    v_currMacroScope_2194_ = leanh::lean_ctor_get(v_a_2130_, 2);
                    v_ref_2195_ = leanh::lean_ctor_get(v_a_2130_, 5);
                    v___x_2196_ = 0;
                    v___x_2197_ = l_Lean_SourceInfo_fromRef(v_ref_2195_, v___x_2196_);
                    v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                    v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    leanh::lean_inc_n(v___x_2197_, 7);
                    v___x_2200_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2200_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                    v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2202_ = l_Lean_Syntax_node1(v___x_2197_, v___x_2201_, v_val_2192_);
                    v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                    v___x_2204_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2204_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2204_, 1, v___x_2203_);
                    v___x_2205_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
                    v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8;
                    leanh::lean_inc(v_currMacroScope_2194_);
                    leanh::lean_inc(v_quotContext_2193_);
                    v___x_2207_ = l_Lean_addMacroScope(
                        v_quotContext_2193_,
                        v___x_2206_,
                        v_currMacroScope_2194_,
                    );
                    v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13;
                    v___x_2209_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2209_, 1, v___x_2205_);
                    leanh::lean_ctor_set(v___x_2209_, 2, v___x_2207_);
                    leanh::lean_ctor_set(v___x_2209_, 3, v___x_2208_);
                    v___x_2210_ =
                        l_Lean_Syntax_node2(v___x_2197_, v___x_2201_, v___x_2204_, v___x_2209_);
                    v___x_2211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2212_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2212_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2212_, 1, v___x_2201_);
                    leanh::lean_ctor_set(v___x_2212_, 2, v___x_2211_);
                    v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2214_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2214_, 0, v___x_2197_);
                    leanh::lean_ctor_set(v___x_2214_, 1, v___x_2213_);
                    v___x_2215_ = l_Lean_Syntax_node5(
                        v___x_2197_,
                        v___x_2198_,
                        v___x_2200_,
                        v___x_2202_,
                        v___x_2210_,
                        v___x_2212_,
                        v___x_2214_,
                    );
                    v___x_2216_ = lean_array_push(v_params_2191_, v___x_2215_);
                    v_params_2135_ = v___x_2216_;
                    v___y_2136_ = v_a_2130_;
                    v___y_2137_ = v_a_2131_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_var_x3f_2132_);
                    v_params_2135_ = v_params_2191_;
                    v___y_2136_ = v_a_2130_;
                    v___y_2137_ = v_a_2131_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2138_ = lean_array_mk(v_pvars_2133_);
                v___x_2139_ = l_Array_reverse___redArg(v___x_2138_);
                v___x_2140_ = leanh::lean_unsigned_to_nat(0);
                v___x_2141_ = lean_array_get_size(v___x_2139_);
                v___x_2142_ =
                    l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
                        v___x_2139_,
                        v___x_2140_,
                        v___x_2141_,
                        v___y_2136_,
                        v___y_2137_,
                    );
                leanh::lean_dec_ref(v___x_2139_);
                if leanh::lean_obj_tag(v___x_2142_) == 0 {
                    v_a_2143_ = leanh::lean_ctor_get(v___x_2142_, 0);
                    v_a_2144_ = leanh::lean_ctor_get(v___x_2142_, 1);
                    v_isSharedCheck_2190_ = (!leanh::lean_is_exclusive(v___x_2142_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2146_ = v___x_2142_;
                        v_isShared_2147_ = v_isSharedCheck_2190_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2144_);
                        leanh::lean_inc(v_a_2143_);
                        leanh::lean_dec(v___x_2142_);
                        v___x_2146_ = leanh::lean_box(0);
                        v_isShared_2147_ = v_isSharedCheck_2190_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_params_2135_);
                    return v___x_2142_;
                }
            }
            2 => {
                v___x_2148_ = l_Array_append___redArg(v_params_2135_, v_a_2143_);
                leanh::lean_dec(v_a_2143_);
                v___x_2149_ = lean_array_get_size(v___x_2148_);
                v___x_2150_ = lean_nat_dec_eq(v___x_2149_, v___x_2140_);
                if v___x_2150_ == 0 {
                    v_sz_2151_ = lean_array_size(v___x_2148_);
                    v___x_2152_ = 0usize;
                    v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_2151_, v___x_2152_, v___x_2148_);
                    if v_isShared_2147_ == 0 {
                        leanh::lean_ctor_set(v___x_2146_, 0, v___x_2153_);
                        v___x_2155_ = v___x_2146_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_a_2144_);
                        v___x_2155_ = v_reuseFailAlloc_2156_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2148_);
                    v_quotContext_2157_ = leanh::lean_ctor_get(v___y_2136_, 1);
                    v_currMacroScope_2158_ = leanh::lean_ctor_get(v___y_2136_, 2);
                    v_ref_2159_ = leanh::lean_ctor_get(v___y_2136_, 5);
                    v___x_2160_ = 0;
                    v___x_2161_ = l_Lean_SourceInfo_fromRef(v_ref_2159_, v___x_2160_);
                    v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                    v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    leanh::lean_inc_n(v___x_2161_, 9);
                    v___x_2164_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2164_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2164_, 1, v___x_2163_);
                    v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2166_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                    v___x_2167_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                    v___x_2168_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2168_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2168_, 1, v___x_2167_);
                    v___x_2169_ = l_Lean_Syntax_node1(v___x_2161_, v___x_2166_, v___x_2168_);
                    v___x_2170_ = l_Lean_Syntax_node1(v___x_2161_, v___x_2165_, v___x_2169_);
                    v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                    v___x_2172_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2172_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
                    v___x_2173_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2,
                    );
                    v___x_2174_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__3;
                    leanh::lean_inc(v_currMacroScope_2158_);
                    leanh::lean_inc(v_quotContext_2157_);
                    v___x_2175_ = l_Lean_addMacroScope(
                        v_quotContext_2157_,
                        v___x_2174_,
                        v_currMacroScope_2158_,
                    );
                    v___x_2176_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__7;
                    v___x_2177_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2177_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2177_, 1, v___x_2173_);
                    leanh::lean_ctor_set(v___x_2177_, 2, v___x_2175_);
                    leanh::lean_ctor_set(v___x_2177_, 3, v___x_2176_);
                    v___x_2178_ =
                        l_Lean_Syntax_node2(v___x_2161_, v___x_2165_, v___x_2172_, v___x_2177_);
                    v___x_2179_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2180_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2180_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2180_, 1, v___x_2165_);
                    leanh::lean_ctor_set(v___x_2180_, 2, v___x_2179_);
                    v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2182_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2161_);
                    leanh::lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                    v___x_2183_ = l_Lean_Syntax_node5(
                        v___x_2161_,
                        v___x_2162_,
                        v___x_2164_,
                        v___x_2170_,
                        v___x_2178_,
                        v___x_2180_,
                        v___x_2182_,
                    );
                    v___x_2184_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2185_ = lean_mk_empty_array_with_capacity(v___x_2184_);
                    v___x_2186_ = lean_array_push(v___x_2185_, v___x_2183_);
                    if v_isShared_2147_ == 0 {
                        leanh::lean_ctor_set(v___x_2146_, 0, v___x_2186_);
                        v___x_2188_ = v___x_2146_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_a_2144_);
                        v___x_2188_ = v_reuseFailAlloc_2189_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2155_;
            }
            4 => {
                return v___x_2188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getParams___boxed(
    mut v_alt_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
    mut v_a_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Lean_Elab_Term_MatchExpr_getParams(v_alt_2217_, v_a_2218_, v_a_2219_);
    leanh::lean_dec_ref(v_a_2218_);
    return v_res_2220_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__6;
    v___x_2238_ = l_String_toRawSubstring_x27(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getActuals(
    mut v_discr_2277_: *mut leanh::LeanObject,
    mut v_alt_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_var_x3f_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: u8 = 0;
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_actuals_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_actuals_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_var_x3f_2281_ = leanh::lean_ctor_get(v_alt_2278_, 0);
                leanh::lean_inc(v_var_x3f_2281_);
                v_actuals_2282_ = leanh::lean_ctor_get(v_alt_2278_, 5);
                leanh::lean_inc(v_actuals_2282_);
                leanh::lean_dec_ref(v_alt_2278_);
                v_actuals_2320_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
                if leanh::lean_obj_tag(v_var_x3f_2281_) == 0 {
                    leanh::lean_dec(v_discr_2277_);
                    v_actuals_2284_ = v_actuals_2320_;
                    v___y_2285_ = v_a_2279_;
                    v___y_2286_ = v_a_2280_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_var_x3f_2281_, 1);
                    v_actuals_2321_ = lean_array_push(v_actuals_2320_, v_discr_2277_);
                    v_actuals_2284_ = v_actuals_2321_;
                    v___y_2285_ = v_a_2279_;
                    v___y_2286_ = v_a_2280_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2287_ = lean_array_mk(v_actuals_2282_);
                v_actuals_2288_ = l_Array_append___redArg(v_actuals_2284_, v___x_2287_);
                leanh::lean_dec_ref(v___x_2287_);
                v___x_2289_ = lean_array_get_size(v_actuals_2288_);
                v___x_2290_ = leanh::lean_unsigned_to_nat(0);
                v___x_2291_ = lean_nat_dec_eq(v___x_2289_, v___x_2290_);
                if v___x_2291_ == 0 {
                    v___x_2292_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2292_, 0, v_actuals_2288_);
                    leanh::lean_ctor_set(v___x_2292_, 1, v___y_2286_);
                    return v___x_2292_;
                } else {
                    leanh::lean_dec_ref(v_actuals_2288_);
                    v_quotContext_2293_ = leanh::lean_ctor_get(v___y_2285_, 1);
                    v_currMacroScope_2294_ = leanh::lean_ctor_get(v___y_2285_, 2);
                    v_ref_2295_ = leanh::lean_ctor_get(v___y_2285_, 5);
                    v___x_2296_ = 0;
                    v___x_2297_ = l_Lean_SourceInfo_fromRef(v_ref_2295_, v___x_2296_);
                    v___x_2298_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                    v___x_2299_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                    v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    leanh::lean_inc_n(v___x_2297_, 6);
                    v___x_2301_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                    v___x_2302_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                    v___x_2303_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                    );
                    v___x_2304_ = leanh::lean_box(0);
                    leanh::lean_inc(v_currMacroScope_2294_);
                    leanh::lean_inc(v_quotContext_2293_);
                    v___x_2305_ = l_Lean_addMacroScope(
                        v_quotContext_2293_,
                        v___x_2304_,
                        v_currMacroScope_2294_,
                    );
                    v___x_2306_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                    v___x_2307_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2307_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v___x_2307_, 1, v___x_2303_);
                    leanh::lean_ctor_set(v___x_2307_, 2, v___x_2305_);
                    leanh::lean_ctor_set(v___x_2307_, 3, v___x_2306_);
                    v___x_2308_ = l_Lean_Syntax_node1(v___x_2297_, v___x_2302_, v___x_2307_);
                    v___x_2309_ =
                        l_Lean_Syntax_node2(v___x_2297_, v___x_2299_, v___x_2301_, v___x_2308_);
                    v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2312_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v___x_2312_, 1, v___x_2310_);
                    leanh::lean_ctor_set(v___x_2312_, 2, v___x_2311_);
                    v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2314_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2314_, 0, v___x_2297_);
                    leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
                    v___x_2315_ = l_Lean_Syntax_node3(
                        v___x_2297_,
                        v___x_2298_,
                        v___x_2309_,
                        v___x_2312_,
                        v___x_2314_,
                    );
                    v___x_2316_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
                    v___x_2318_ = lean_array_push(v___x_2317_, v___x_2315_);
                    v___x_2319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2319_, 0, v___x_2318_);
                    leanh::lean_ctor_set(v___x_2319_, 1, v___y_2286_);
                    return v___x_2319_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getActuals___boxed(
    mut v_discr_2322_: *mut leanh::LeanObject,
    mut v_alt_2323_: *mut leanh::LeanObject,
    mut v_a_2324_: *mut leanh::LeanObject,
    mut v_a_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ =
        l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_2322_, v_alt_2323_, v_a_2324_, v_a_2325_);
    leanh::lean_dec_ref(v_a_2324_);
    return v_res_2326_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2;
    v___x_2335_ = l_Lean_mkAtom(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3,
    );
    v___x_2337_ = leanh::lean_unsigned_to_nat(3);
    v___x_2338_ = lean_mk_empty_array_with_capacity(v___x_2337_);
    v___x_2339_ = lean_array_push(v___x_2338_, v___x_2336_);
    return v___x_2339_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2340_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3,
    );
    v___x_2341_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4,
    );
    v___x_2342_ = lean_array_push(v___x_2341_, v___x_2340_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(
    mut v_ident_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1;
    v___x_2345_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5,
    );
    v___x_2346_ = lean_array_push(v___x_2345_, v_ident_2343_);
    v___x_2347_ = leanh::lean_box(2);
    v___x_2348_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2348_, 0, v___x_2347_);
    leanh::lean_ctor_set(v___x_2348_, 1, v___x_2344_);
    leanh::lean_ctor_set(v___x_2348_, 2, v___x_2346_);
    return v___x_2348_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(
    mut v___x_2349_: u8,
    mut v_____do__lift_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2350_, v___x_2349_);
    v___x_2354_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    leanh::lean_ctor_set(v___x_2354_, 1, v___y_2352_);
    return v___x_2354_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(
    mut v___x_2355_: *mut leanh::LeanObject,
    mut v_____do__lift_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_20980__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_20980__boxed_2359_ = (leanh::lean_unbox(v___x_2355_) as u8);
    v_res_2360_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(
            v___x_20980__boxed_2359_,
            v_____do__lift_2356_,
            v___y_2357_,
            v___y_2358_,
        );
    leanh::lean_dec_ref(v___y_2357_);
    leanh::lean_dec(v_____do__lift_2356_);
    return v_res_2360_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8;
    v___x_2383_ = l_String_toRawSubstring_x27(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(
    mut v_alts_2391_: *mut leanh::LeanObject,
    mut v_discr_2392_: *mut leanh::LeanObject,
    mut v_as_x27_2393_: *mut leanh::LeanObject,
    mut v_b_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
    mut v___y_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v_quotContext_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2393_) == 0 {
                    leanh::lean_dec(v_discr_2392_);
                    v___x_2397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2397_, 0, v_b_2394_);
                    leanh::lean_ctor_set(v___x_2397_, 1, v___y_2396_);
                    return v___x_2397_;
                } else {
                    v_head_2398_ = leanh::lean_ctor_get(v_as_x27_2393_, 0);
                    v_tail_2399_ = leanh::lean_ctor_get(v_as_x27_2393_, 1);
                    v___x_2400_ =
                        l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
                            v_head_2398_,
                            v_alts_2391_,
                        );
                    if leanh::lean_obj_tag(v___x_2400_) == 1 {
                        v_val_2401_ = leanh::lean_ctor_get(v___x_2400_, 0);
                        leanh::lean_inc_n(v_val_2401_, 2);
                        leanh::lean_dec_ref_known(v___x_2400_, 1);
                        leanh::lean_inc(v_discr_2392_);
                        v___x_2402_ = l_Lean_Elab_Term_MatchExpr_getActuals(
                            v_discr_2392_,
                            v_val_2401_,
                            v___y_2395_,
                            v___y_2396_,
                        );
                        v_a_2403_ = leanh::lean_ctor_get(v___x_2402_, 0);
                        v_a_2404_ = leanh::lean_ctor_get(v___x_2402_, 1);
                        v_isSharedCheck_2458_ =
                            (!leanh::lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2458_ == 0 {
                            v___x_2406_ = v___x_2402_;
                            v_isShared_2407_ = v_isSharedCheck_2458_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2404_);
                            leanh::lean_inc(v_a_2403_);
                            leanh::lean_dec(v___x_2402_);
                            v___x_2406_ = leanh::lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2400_);
                        v_as_x27_2393_ = v_tail_2399_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_2408_ = leanh::lean_ctor_get(v___y_2395_, 1);
                v_currMacroScope_2409_ = leanh::lean_ctor_get(v___y_2395_, 2);
                v_ref_2410_ = leanh::lean_ctor_get(v___y_2395_, 5);
                v___x_2411_ = 0;
                v___x_2412_ = l_Lean_SourceInfo_fromRef(v_ref_2410_, v___x_2411_);
                v___x_2413_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                leanh::lean_inc(v___x_2412_);
                if v_isShared_2407_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2406_, 2);
                    leanh::lean_ctor_set(v___x_2406_, 1, v___x_2413_);
                    leanh::lean_ctor_set(v___x_2406_, 0, v___x_2412_);
                    v___x_2415_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2413_);
                    v___x_2415_ = v_reuseFailAlloc_2457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2416_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_2417_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4;
                v___x_2418_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6;
                v___x_2419_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                leanh::lean_inc_n(v___x_2412_, 15);
                v___x_2421_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2421_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2421_, 1, v___x_2420_);
                v___x_2422_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2423_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2424_ = leanh::lean_box(0);
                leanh::lean_inc_n(v_currMacroScope_2409_, 2);
                leanh::lean_inc_n(v_quotContext_2408_, 2);
                v___x_2425_ =
                    l_Lean_addMacroScope(v_quotContext_2408_, v___x_2424_, v_currMacroScope_2409_);
                v___x_2426_ = leanh::lean_box(0);
                v___x_2427_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2428_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2428_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2428_, 1, v___x_2423_);
                leanh::lean_ctor_set(v___x_2428_, 2, v___x_2425_);
                leanh::lean_ctor_set(v___x_2428_, 3, v___x_2427_);
                v___x_2429_ = l_Lean_Syntax_node1(v___x_2412_, v___x_2422_, v___x_2428_);
                v___x_2430_ =
                    l_Lean_Syntax_node2(v___x_2412_, v___x_2419_, v___x_2421_, v___x_2429_);
                v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2432_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2432_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2432_, 1, v___x_2431_);
                leanh::lean_inc(v_discr_2392_);
                v___x_2433_ = l_Lean_Syntax_node3(
                    v___x_2412_,
                    v___x_2418_,
                    v___x_2430_,
                    v_discr_2392_,
                    v___x_2432_,
                );
                v___x_2434_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2435_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2435_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2435_, 1, v___x_2434_);
                v___x_2436_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9);
                v___x_2437_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10;
                v___x_2438_ =
                    l_Lean_addMacroScope(v_quotContext_2408_, v___x_2437_, v_currMacroScope_2409_);
                v___x_2439_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2439_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2439_, 1, v___x_2436_);
                leanh::lean_ctor_set(v___x_2439_, 2, v___x_2438_);
                leanh::lean_ctor_set(v___x_2439_, 3, v___x_2426_);
                v___x_2440_ = l_Lean_Syntax_node3(
                    v___x_2412_,
                    v___x_2417_,
                    v___x_2433_,
                    v___x_2435_,
                    v___x_2439_,
                );
                v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                leanh::lean_inc(v_head_2398_);
                v___x_2442_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(v_head_2398_);
                v___x_2443_ = l_Lean_Syntax_node1(v___x_2412_, v___x_2441_, v___x_2442_);
                v_k_2444_ = leanh::lean_ctor_get(v_val_2401_, 4);
                leanh::lean_inc(v_k_2444_);
                leanh::lean_dec(v_val_2401_);
                v___x_2445_ =
                    l_Lean_Syntax_node2(v___x_2412_, v___x_2416_, v___x_2440_, v___x_2443_);
                v___x_2446_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12;
                v___x_2447_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2448_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2448_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2448_, 1, v___x_2447_);
                v___x_2449_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2450_ = l_Array_append___redArg(v___x_2449_, v_a_2403_);
                leanh::lean_dec(v_a_2403_);
                v___x_2451_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2451_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2451_, 1, v___x_2441_);
                leanh::lean_ctor_set(v___x_2451_, 2, v___x_2450_);
                v___x_2452_ = l_Lean_Syntax_node2(v___x_2412_, v___x_2416_, v_k_2444_, v___x_2451_);
                v___x_2453_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14;
                v___x_2454_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2454_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                v___x_2455_ = l_Lean_Syntax_node6(
                    v___x_2412_,
                    v___x_2446_,
                    v___x_2415_,
                    v___x_2445_,
                    v___x_2448_,
                    v___x_2452_,
                    v___x_2454_,
                    v_b_2394_,
                );
                v_as_x27_2393_ = v_tail_2399_;
                v_b_2394_ = v___x_2455_;
                v___y_2396_ = v_a_2404_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___boxed(
    mut v_alts_2460_: *mut leanh::LeanObject,
    mut v_discr_2461_: *mut leanh::LeanObject,
    mut v_as_x27_2462_: *mut leanh::LeanObject,
    mut v_b_2463_: *mut leanh::LeanObject,
    mut v___y_2464_: *mut leanh::LeanObject,
    mut v___y_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2460_, v_discr_2461_, v_as_x27_2462_, v_b_2463_, v___y_2464_, v___y_2465_);
    leanh::lean_dec_ref(v___y_2464_);
    leanh::lean_dec(v_as_x27_2462_);
    leanh::lean_dec(v_alts_2460_);
    return v_res_2466_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0;
    v___x_2469_ = l_String_toRawSubstring_x27(v___x_2468_);
    return v___x_2469_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7;
    v___x_2481_ = l_String_toRawSubstring_x27(v___x_2480_);
    return v___x_2481_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10;
    v___x_2486_ = l_String_toRawSubstring_x27(v___x_2485_);
    return v___x_2486_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24;
    v___x_2522_ = l_String_toRawSubstring_x27(v___x_2521_);
    return v___x_2522_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32;
    v___x_2540_ = l_String_toRawSubstring_x27(v___x_2539_);
    return v___x_2540_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35;
    v___x_2545_ = l_String_toRawSubstring_x27(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
    mut v_kElse_2560_: *mut leanh::LeanObject,
    mut v_discr_2561_: *mut leanh::LeanObject,
    mut v_alts_2562_: *mut leanh::LeanObject,
    mut v_a_2563_: *mut leanh::LeanObject,
    mut v_a_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_macroScope_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v_methods_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funNamesToMatch_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveActual_2577_: u8 = 0;
    let mut v_actual_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_altsNext_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v_quotContext_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_a_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v_quotContext_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_2565_ = leanh::lean_ctor_get(v_a_2564_, 0);
                v_traceMsgs_2566_ = leanh::lean_ctor_get(v_a_2564_, 1);
                v_expandedMacroDecls_2567_ = leanh::lean_ctor_get(v_a_2564_, 2);
                v_isSharedCheck_2837_ = (!leanh::lean_is_exclusive(v_a_2564_)) as u8;
                if v_isSharedCheck_2837_ == 0 {
                    v___x_2569_ = v_a_2564_;
                    v_isShared_2570_ = v_isSharedCheck_2837_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expandedMacroDecls_2567_);
                    leanh::lean_inc(v_traceMsgs_2566_);
                    leanh::lean_inc(v_macroScope_2565_);
                    leanh::lean_dec(v_a_2564_);
                    v___x_2569_ = leanh::lean_box(0);
                    v_isShared_2570_ = v_isSharedCheck_2837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_methods_2571_ = leanh::lean_ctor_get(v_a_2563_, 0);
                v_quotContext_2572_ = leanh::lean_ctor_get(v_a_2563_, 1);
                v_currRecDepth_2573_ = leanh::lean_ctor_get(v_a_2563_, 3);
                v_maxRecDepth_2574_ = leanh::lean_ctor_get(v_a_2563_, 4);
                v_ref_2575_ = leanh::lean_ctor_get(v_a_2563_, 5);
                v_funNamesToMatch_2576_ =
                    l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_2562_);
                v_saveActual_2577_ =
                    l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(
                        v_alts_2562_,
                    );
                v___x_2819_ = leanh::lean_unsigned_to_nat(1);
                v___x_2820_ = lean_nat_add(v_macroScope_2565_, v___x_2819_);
                if v_isShared_2570_ == 0 {
                    leanh::lean_ctor_set(v___x_2569_, 0, v___x_2820_);
                    v___x_2822_ = v___x_2569_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2836_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_traceMsgs_2566_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2836_,
                        2,
                        v_expandedMacroDecls_2567_,
                    );
                    v___x_2822_ = v_reuseFailAlloc_2836_;
                    state = 11;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_alts_2562_);
                v_altsNext_2582_ = l_Lean_Elab_Term_MatchExpr_next(v_alts_2562_, v_actual_2579_);
                v___x_2583_ = l_List_isEmpty___redArg(v_altsNext_2582_);
                if v___x_2583_ == 0 {
                    v_quotContext_2584_ = leanh::lean_ctor_get(v___y_2580_, 1);
                    v_currMacroScope_2585_ = leanh::lean_ctor_get(v___y_2580_, 2);
                    v_ref_2586_ = leanh::lean_ctor_get(v___y_2580_, 5);
                    v___x_2587_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_2583_, v_ref_2586_, v___y_2580_, v___y_2581_);
                    if leanh::lean_obj_tag(v___x_2587_) == 0 {
                        v_a_2588_ = leanh::lean_ctor_get(v___x_2587_, 0);
                        leanh::lean_inc(v_a_2588_);
                        v_a_2589_ = leanh::lean_ctor_get(v___x_2587_, 1);
                        leanh::lean_inc(v_a_2589_);
                        leanh::lean_dec_ref_known(v___x_2587_, 2);
                        v___x_2590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
                        v___x_2591_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2;
                        leanh::lean_inc(v_currMacroScope_2585_);
                        leanh::lean_inc(v_quotContext_2584_);
                        v___x_2592_ = l_Lean_addMacroScope(
                            v_quotContext_2584_,
                            v___x_2591_,
                            v_currMacroScope_2585_,
                        );
                        v___x_2593_ = leanh::lean_box(0);
                        leanh::lean_inc(v___x_2592_);
                        v___x_2594_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_2594_, 0, v_a_2588_);
                        leanh::lean_ctor_set(v___x_2594_, 1, v___x_2590_);
                        leanh::lean_ctor_set(v___x_2594_, 2, v___x_2592_);
                        leanh::lean_ctor_set(v___x_2594_, 3, v___x_2593_);
                        leanh::lean_inc(v_kElse_2560_);
                        v___x_2595_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_2560_, v___x_2594_, v_altsNext_2582_, v___y_2580_, v_a_2589_);
                        if leanh::lean_obj_tag(v___x_2595_) == 0 {
                            if v_saveActual_2577_ == 0 {
                                v_a_2596_ = leanh::lean_ctor_get(v___x_2595_, 0);
                                v_a_2597_ = leanh::lean_ctor_get(v___x_2595_, 1);
                                v_isSharedCheck_2676_ =
                                    (!leanh::lean_is_exclusive(v___x_2595_)) as u8;
                                if v_isSharedCheck_2676_ == 0 {
                                    v___x_2599_ = v___x_2595_;
                                    v_isShared_2600_ = v_isSharedCheck_2676_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2597_);
                                    leanh::lean_inc(v_a_2596_);
                                    leanh::lean_dec(v___x_2595_);
                                    v___x_2599_ = leanh::lean_box(0);
                                    v_isShared_2600_ = v_isSharedCheck_2676_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_2677_ = leanh::lean_ctor_get(v___x_2595_, 0);
                                v_a_2678_ = leanh::lean_ctor_get(v___x_2595_, 1);
                                v_isSharedCheck_2782_ =
                                    (!leanh::lean_is_exclusive(v___x_2595_)) as u8;
                                if v_isSharedCheck_2782_ == 0 {
                                    v___x_2680_ = v___x_2595_;
                                    v_isShared_2681_ = v_isSharedCheck_2782_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2678_);
                                    leanh::lean_inc(v_a_2677_);
                                    leanh::lean_dec(v___x_2595_);
                                    v___x_2680_ = leanh::lean_box(0);
                                    v_isShared_2681_ = v_isSharedCheck_2782_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2592_);
                            leanh::lean_dec_ref(v___y_2580_);
                            leanh::lean_dec(v_funNamesToMatch_2576_);
                            leanh::lean_dec(v_alts_2562_);
                            leanh::lean_dec(v_discr_2561_);
                            leanh::lean_dec(v_kElse_2560_);
                            return v___x_2595_;
                        }
                    } else {
                        leanh::lean_dec(v_altsNext_2582_);
                        leanh::lean_dec_ref(v___y_2580_);
                        leanh::lean_dec(v_funNamesToMatch_2576_);
                        leanh::lean_dec(v_alts_2562_);
                        leanh::lean_dec(v_discr_2561_);
                        leanh::lean_dec(v_kElse_2560_);
                        v_a_2783_ = leanh::lean_ctor_get(v___x_2587_, 0);
                        v_a_2784_ = leanh::lean_ctor_get(v___x_2587_, 1);
                        v_isSharedCheck_2791_ =
                            (!leanh::lean_is_exclusive(v___x_2587_)) as u8;
                        if v_isSharedCheck_2791_ == 0 {
                            v___x_2786_ = v___x_2587_;
                            v_isShared_2787_ = v_isSharedCheck_2791_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2784_);
                            leanh::lean_inc(v_a_2783_);
                            leanh::lean_dec(v___x_2587_);
                            v___x_2786_ = leanh::lean_box(0);
                            v_isShared_2787_ = v_isSharedCheck_2791_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_altsNext_2582_);
                    v_quotContext_2792_ = leanh::lean_ctor_get(v___y_2580_, 1);
                    v_currMacroScope_2793_ = leanh::lean_ctor_get(v___y_2580_, 2);
                    v_ref_2794_ = leanh::lean_ctor_get(v___y_2580_, 5);
                    v___x_2795_ = 0;
                    v___x_2796_ = l_Lean_SourceInfo_fromRef(v_ref_2794_, v___x_2795_);
                    v___x_2797_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                    v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2799_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                    v___x_2800_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                    v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    leanh::lean_inc_n(v___x_2796_, 8);
                    v___x_2802_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2802_, 0, v___x_2796_);
                    leanh::lean_ctor_set(v___x_2802_, 1, v___x_2801_);
                    v___x_2803_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                    v___x_2804_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                    );
                    v___x_2805_ = leanh::lean_box(0);
                    leanh::lean_inc(v_currMacroScope_2793_);
                    leanh::lean_inc(v_quotContext_2792_);
                    v___x_2806_ = l_Lean_addMacroScope(
                        v_quotContext_2792_,
                        v___x_2805_,
                        v_currMacroScope_2793_,
                    );
                    v___x_2807_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                    v___x_2808_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2808_, 0, v___x_2796_);
                    leanh::lean_ctor_set(v___x_2808_, 1, v___x_2804_);
                    leanh::lean_ctor_set(v___x_2808_, 2, v___x_2806_);
                    leanh::lean_ctor_set(v___x_2808_, 3, v___x_2807_);
                    v___x_2809_ = l_Lean_Syntax_node1(v___x_2796_, v___x_2803_, v___x_2808_);
                    v___x_2810_ =
                        l_Lean_Syntax_node2(v___x_2796_, v___x_2800_, v___x_2802_, v___x_2809_);
                    v___x_2811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2812_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2812_, 0, v___x_2796_);
                    leanh::lean_ctor_set(v___x_2812_, 1, v___x_2798_);
                    leanh::lean_ctor_set(v___x_2812_, 2, v___x_2811_);
                    v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2814_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2814_, 0, v___x_2796_);
                    leanh::lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                    v___x_2815_ = l_Lean_Syntax_node3(
                        v___x_2796_,
                        v___x_2799_,
                        v___x_2810_,
                        v___x_2812_,
                        v___x_2814_,
                    );
                    v___x_2816_ = l_Lean_Syntax_node1(v___x_2796_, v___x_2798_, v___x_2815_);
                    v___x_2817_ =
                        l_Lean_Syntax_node2(v___x_2796_, v___x_2797_, v_kElse_2560_, v___x_2816_);
                    v___x_2818_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2562_, v_discr_2561_, v_funNamesToMatch_2576_, v___x_2817_, v___y_2580_, v___y_2581_);
                    leanh::lean_dec_ref(v___y_2580_);
                    leanh::lean_dec(v_funNamesToMatch_2576_);
                    leanh::lean_dec(v_alts_2562_);
                    return v___x_2818_;
                }
            }
            3 => {
                v___x_2601_ = l_Lean_SourceInfo_fromRef(v_ref_2586_, v_saveActual_2577_);
                v___x_2602_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4;
                v___x_2603_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                leanh::lean_inc(v___x_2601_);
                if v_isShared_2600_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2599_, 2);
                    leanh::lean_ctor_set(v___x_2599_, 1, v___x_2603_);
                    leanh::lean_ctor_set(v___x_2599_, 0, v___x_2601_);
                    v___x_2605_ = v___x_2599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2603_);
                    v___x_2605_ = v_reuseFailAlloc_2675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2606_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6;
                v___x_2607_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
                v___x_2608_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9;
                leanh::lean_inc_n(v_currMacroScope_2585_, 4);
                leanh::lean_inc_n(v_quotContext_2584_, 4);
                v___x_2609_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2608_, v_currMacroScope_2585_);
                leanh::lean_inc_n(v___x_2601_, 30);
                v___x_2610_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2610_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2610_, 1, v___x_2607_);
                leanh::lean_ctor_set(v___x_2610_, 2, v___x_2609_);
                leanh::lean_ctor_set(v___x_2610_, 3, v___x_2593_);
                leanh::lean_inc_ref(v___x_2610_);
                v___x_2611_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2606_, v___x_2610_);
                v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_2613_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2613_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                v___x_2614_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4;
                v___x_2615_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6;
                v___x_2616_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                v___x_2618_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2618_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2618_, 1, v___x_2617_);
                v___x_2619_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2620_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2621_ = leanh::lean_box(0);
                v___x_2622_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2621_, v_currMacroScope_2585_);
                v___x_2623_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2624_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2624_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2624_, 1, v___x_2620_);
                leanh::lean_ctor_set(v___x_2624_, 2, v___x_2622_);
                leanh::lean_ctor_set(v___x_2624_, 3, v___x_2623_);
                v___x_2625_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2619_, v___x_2624_);
                v___x_2626_ =
                    l_Lean_Syntax_node2(v___x_2601_, v___x_2616_, v___x_2618_, v___x_2625_);
                v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2628_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2628_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                leanh::lean_inc_ref(v___x_2628_);
                leanh::lean_inc_n(v_discr_2561_, 2);
                leanh::lean_inc(v___x_2626_);
                v___x_2629_ = l_Lean_Syntax_node3(
                    v___x_2601_,
                    v___x_2615_,
                    v___x_2626_,
                    v_discr_2561_,
                    v___x_2628_,
                );
                v___x_2630_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2631_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2631_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2631_, 1, v___x_2630_);
                v___x_2632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
                v___x_2633_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12;
                v___x_2634_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2633_, v_currMacroScope_2585_);
                v___x_2635_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2635_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2635_, 1, v___x_2632_);
                leanh::lean_ctor_set(v___x_2635_, 2, v___x_2634_);
                leanh::lean_ctor_set(v___x_2635_, 3, v___x_2593_);
                v___x_2636_ = l_Lean_Syntax_node3(
                    v___x_2601_,
                    v___x_2614_,
                    v___x_2629_,
                    v___x_2631_,
                    v___x_2635_,
                );
                v___x_2637_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2638_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2638_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                v___x_2639_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_2640_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_2641_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2641_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2641_, 1, v___x_2639_);
                v___x_2642_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_2644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2645_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2645_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2645_, 1, v___x_2643_);
                leanh::lean_ctor_set(v___x_2645_, 2, v___x_2644_);
                leanh::lean_inc_ref_n(v___x_2645_, 3);
                v___x_2646_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2642_, v___x_2645_);
                v___x_2647_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_2648_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_2649_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                v___x_2650_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2650_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2650_, 1, v___x_2590_);
                leanh::lean_ctor_set(v___x_2650_, 2, v___x_2592_);
                leanh::lean_ctor_set(v___x_2650_, 3, v___x_2593_);
                v___x_2651_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2649_, v___x_2650_);
                v___x_2652_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                v___x_2653_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2653_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2653_, 1, v___x_2652_);
                v___x_2654_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_2655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
                v___x_2656_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27;
                v___x_2657_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2656_, v_currMacroScope_2585_);
                v___x_2658_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30;
                v___x_2659_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2659_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2659_, 1, v___x_2655_);
                leanh::lean_ctor_set(v___x_2659_, 2, v___x_2657_);
                leanh::lean_ctor_set(v___x_2659_, 3, v___x_2658_);
                v___x_2660_ =
                    l_Lean_Syntax_node2(v___x_2601_, v___x_2643_, v_discr_2561_, v___x_2610_);
                v___x_2661_ =
                    l_Lean_Syntax_node2(v___x_2601_, v___x_2654_, v___x_2659_, v___x_2660_);
                v___x_2662_ = l_Lean_Syntax_node5(
                    v___x_2601_,
                    v___x_2648_,
                    v___x_2651_,
                    v___x_2645_,
                    v___x_2645_,
                    v___x_2653_,
                    v___x_2661_,
                );
                v___x_2663_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2647_, v___x_2662_);
                v___x_2664_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31;
                v___x_2665_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2665_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2665_, 1, v___x_2664_);
                v___x_2666_ = l_Lean_Syntax_node5(
                    v___x_2601_,
                    v___x_2640_,
                    v___x_2641_,
                    v___x_2646_,
                    v___x_2663_,
                    v___x_2665_,
                    v_a_2596_,
                );
                v___x_2667_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14;
                v___x_2668_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2668_, 0, v___x_2601_);
                leanh::lean_ctor_set(v___x_2668_, 1, v___x_2667_);
                v___x_2669_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                v___x_2670_ = l_Lean_Syntax_node3(
                    v___x_2601_,
                    v___x_2669_,
                    v___x_2626_,
                    v___x_2645_,
                    v___x_2628_,
                );
                v___x_2671_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2643_, v___x_2670_);
                v___x_2672_ =
                    l_Lean_Syntax_node2(v___x_2601_, v___x_2654_, v_kElse_2560_, v___x_2671_);
                v___x_2673_ = l_Lean_Syntax_node8(
                    v___x_2601_,
                    v___x_2602_,
                    v___x_2605_,
                    v___x_2611_,
                    v___x_2613_,
                    v___x_2636_,
                    v___x_2638_,
                    v___x_2666_,
                    v___x_2668_,
                    v___x_2672_,
                );
                v___x_2674_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2562_, v_discr_2561_, v_funNamesToMatch_2576_, v___x_2673_, v___y_2580_, v_a_2597_);
                leanh::lean_dec_ref(v___y_2580_);
                leanh::lean_dec(v_funNamesToMatch_2576_);
                leanh::lean_dec(v_alts_2562_);
                return v___x_2674_;
            }
            5 => {
                v___x_2682_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_2583_, v_ref_2586_, v___y_2580_, v_a_2678_);
                if leanh::lean_obj_tag(v___x_2682_) == 0 {
                    v_a_2683_ = leanh::lean_ctor_get(v___x_2682_, 0);
                    leanh::lean_inc_n(v_a_2683_, 2);
                    v_a_2684_ = leanh::lean_ctor_get(v___x_2682_, 1);
                    leanh::lean_inc(v_a_2684_);
                    leanh::lean_dec_ref_known(v___x_2682_, 2);
                    v___x_2685_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4;
                    v___x_2686_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                    if v_isShared_2681_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2680_, 2);
                        leanh::lean_ctor_set(v___x_2680_, 1, v___x_2686_);
                        leanh::lean_ctor_set(v___x_2680_, 0, v_a_2683_);
                        v___x_2688_ = v___x_2680_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2772_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2683_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2686_);
                        v___x_2688_ = v_reuseFailAlloc_2772_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2680_);
                    leanh::lean_dec(v_a_2677_);
                    leanh::lean_dec(v___x_2592_);
                    leanh::lean_dec_ref(v___y_2580_);
                    leanh::lean_dec(v_funNamesToMatch_2576_);
                    leanh::lean_dec(v_alts_2562_);
                    leanh::lean_dec(v_discr_2561_);
                    leanh::lean_dec(v_kElse_2560_);
                    v_a_2773_ = leanh::lean_ctor_get(v___x_2682_, 0);
                    v_a_2774_ = leanh::lean_ctor_get(v___x_2682_, 1);
                    v_isSharedCheck_2781_ = (!leanh::lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2781_ == 0 {
                        v___x_2776_ = v___x_2682_;
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2774_);
                        leanh::lean_inc(v_a_2773_);
                        leanh::lean_dec(v___x_2682_);
                        v___x_2776_ = leanh::lean_box(0);
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2689_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6;
                v___x_2690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
                v___x_2691_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9;
                leanh::lean_inc_n(v_currMacroScope_2585_, 6);
                leanh::lean_inc_n(v_quotContext_2584_, 6);
                v___x_2692_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2691_, v_currMacroScope_2585_);
                leanh::lean_inc_n(v_a_2683_, 37);
                v___x_2693_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2693_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2693_, 1, v___x_2690_);
                leanh::lean_ctor_set(v___x_2693_, 2, v___x_2692_);
                leanh::lean_ctor_set(v___x_2693_, 3, v___x_2593_);
                leanh::lean_inc_ref(v___x_2693_);
                v___x_2694_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2689_, v___x_2693_);
                v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_2696_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2696_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2696_, 1, v___x_2695_);
                v___x_2697_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4;
                v___x_2698_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6;
                v___x_2699_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                v___x_2701_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2701_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2701_, 1, v___x_2700_);
                v___x_2702_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2703_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2704_ = leanh::lean_box(0);
                v___x_2705_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2704_, v_currMacroScope_2585_);
                v___x_2706_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2707_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2707_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2707_, 1, v___x_2703_);
                leanh::lean_ctor_set(v___x_2707_, 2, v___x_2705_);
                leanh::lean_ctor_set(v___x_2707_, 3, v___x_2706_);
                v___x_2708_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2702_, v___x_2707_);
                v___x_2709_ = l_Lean_Syntax_node2(v_a_2683_, v___x_2699_, v___x_2701_, v___x_2708_);
                v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2711_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2711_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2711_, 1, v___x_2710_);
                leanh::lean_inc_ref(v___x_2711_);
                leanh::lean_inc_n(v_discr_2561_, 2);
                leanh::lean_inc(v___x_2709_);
                v___x_2712_ = l_Lean_Syntax_node3(
                    v_a_2683_,
                    v___x_2698_,
                    v___x_2709_,
                    v_discr_2561_,
                    v___x_2711_,
                );
                v___x_2713_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2714_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2714_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
                v___x_2716_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12;
                v___x_2717_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2716_, v_currMacroScope_2585_);
                v___x_2718_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2718_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2718_, 1, v___x_2715_);
                leanh::lean_ctor_set(v___x_2718_, 2, v___x_2717_);
                leanh::lean_ctor_set(v___x_2718_, 3, v___x_2593_);
                v___x_2719_ = l_Lean_Syntax_node3(
                    v_a_2683_,
                    v___x_2697_,
                    v___x_2712_,
                    v___x_2714_,
                    v___x_2718_,
                );
                v___x_2720_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2721_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2721_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                v___x_2722_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_2723_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_2724_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2724_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2724_, 1, v___x_2722_);
                v___x_2725_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_2727_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2728_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2728_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2728_, 1, v___x_2726_);
                leanh::lean_ctor_set(v___x_2728_, 2, v___x_2727_);
                leanh::lean_inc_ref_n(v___x_2728_, 5);
                v___x_2729_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2725_, v___x_2728_);
                v___x_2730_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_2731_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_2732_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                v___x_2733_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
                v___x_2734_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34;
                v___x_2735_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2734_, v_currMacroScope_2585_);
                v___x_2736_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2736_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2736_, 1, v___x_2733_);
                leanh::lean_ctor_set(v___x_2736_, 2, v___x_2735_);
                leanh::lean_ctor_set(v___x_2736_, 3, v___x_2593_);
                v___x_2737_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2732_, v___x_2736_);
                v___x_2738_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                v___x_2739_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2739_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2739_, 1, v___x_2738_);
                v___x_2740_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_2741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36);
                v___x_2742_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38;
                v___x_2743_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2742_, v_currMacroScope_2585_);
                v___x_2744_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41;
                v___x_2745_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2745_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2745_, 1, v___x_2741_);
                leanh::lean_ctor_set(v___x_2745_, 2, v___x_2743_);
                leanh::lean_ctor_set(v___x_2745_, 3, v___x_2744_);
                v___x_2746_ =
                    l_Lean_Syntax_node2(v_a_2683_, v___x_2726_, v_discr_2561_, v___x_2693_);
                leanh::lean_inc(v___x_2746_);
                v___x_2747_ = l_Lean_Syntax_node2(v_a_2683_, v___x_2740_, v___x_2745_, v___x_2746_);
                leanh::lean_inc_ref(v___x_2739_);
                v___x_2748_ = l_Lean_Syntax_node5(
                    v_a_2683_,
                    v___x_2731_,
                    v___x_2737_,
                    v___x_2728_,
                    v___x_2728_,
                    v___x_2739_,
                    v___x_2747_,
                );
                v___x_2749_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2730_, v___x_2748_);
                v___x_2750_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31;
                v___x_2751_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2751_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2751_, 1, v___x_2750_);
                v___x_2752_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2752_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2752_, 1, v___x_2590_);
                leanh::lean_ctor_set(v___x_2752_, 2, v___x_2592_);
                leanh::lean_ctor_set(v___x_2752_, 3, v___x_2593_);
                v___x_2753_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2732_, v___x_2752_);
                v___x_2754_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
                v___x_2755_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27;
                v___x_2756_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2755_, v_currMacroScope_2585_);
                v___x_2757_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30;
                v___x_2758_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2758_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2758_, 1, v___x_2754_);
                leanh::lean_ctor_set(v___x_2758_, 2, v___x_2756_);
                leanh::lean_ctor_set(v___x_2758_, 3, v___x_2757_);
                v___x_2759_ = l_Lean_Syntax_node2(v_a_2683_, v___x_2740_, v___x_2758_, v___x_2746_);
                v___x_2760_ = l_Lean_Syntax_node5(
                    v_a_2683_,
                    v___x_2731_,
                    v___x_2753_,
                    v___x_2728_,
                    v___x_2728_,
                    v___x_2739_,
                    v___x_2759_,
                );
                v___x_2761_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2730_, v___x_2760_);
                leanh::lean_inc_ref(v___x_2751_);
                leanh::lean_inc(v___x_2729_);
                leanh::lean_inc_ref(v___x_2724_);
                v___x_2762_ = l_Lean_Syntax_node5(
                    v_a_2683_,
                    v___x_2723_,
                    v___x_2724_,
                    v___x_2729_,
                    v___x_2761_,
                    v___x_2751_,
                    v_a_2677_,
                );
                v___x_2763_ = l_Lean_Syntax_node5(
                    v_a_2683_,
                    v___x_2723_,
                    v___x_2724_,
                    v___x_2729_,
                    v___x_2749_,
                    v___x_2751_,
                    v___x_2762_,
                );
                v___x_2764_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14;
                v___x_2765_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2765_, 0, v_a_2683_);
                leanh::lean_ctor_set(v___x_2765_, 1, v___x_2764_);
                v___x_2766_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                v___x_2767_ = l_Lean_Syntax_node3(
                    v_a_2683_,
                    v___x_2766_,
                    v___x_2709_,
                    v___x_2728_,
                    v___x_2711_,
                );
                v___x_2768_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2726_, v___x_2767_);
                v___x_2769_ =
                    l_Lean_Syntax_node2(v_a_2683_, v___x_2740_, v_kElse_2560_, v___x_2768_);
                v___x_2770_ = l_Lean_Syntax_node8(
                    v_a_2683_,
                    v___x_2685_,
                    v___x_2688_,
                    v___x_2694_,
                    v___x_2696_,
                    v___x_2719_,
                    v___x_2721_,
                    v___x_2763_,
                    v___x_2765_,
                    v___x_2769_,
                );
                v___x_2771_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2562_, v_discr_2561_, v_funNamesToMatch_2576_, v___x_2770_, v___y_2580_, v_a_2684_);
                leanh::lean_dec_ref(v___y_2580_);
                leanh::lean_dec(v_funNamesToMatch_2576_);
                leanh::lean_dec(v_alts_2562_);
                return v___x_2771_;
            }
            7 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_a_2774_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2779_;
            }
            9 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2789_;
            }
            11 => {
                leanh::lean_inc(v_ref_2575_);
                leanh::lean_inc(v_maxRecDepth_2574_);
                leanh::lean_inc(v_currRecDepth_2573_);
                leanh::lean_inc(v_macroScope_2565_);
                leanh::lean_inc(v_quotContext_2572_);
                leanh::lean_inc(v_methods_2571_);
                v___x_2823_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_2823_, 0, v_methods_2571_);
                leanh::lean_ctor_set(v___x_2823_, 1, v_quotContext_2572_);
                leanh::lean_ctor_set(v___x_2823_, 2, v_macroScope_2565_);
                leanh::lean_ctor_set(v___x_2823_, 3, v_currRecDepth_2573_);
                leanh::lean_ctor_set(v___x_2823_, 4, v_maxRecDepth_2574_);
                leanh::lean_ctor_set(v___x_2823_, 5, v_ref_2575_);
                if v_saveActual_2577_ == 0 {
                    leanh::lean_dec(v_macroScope_2565_);
                    v___x_2824_ = l_Lean_SourceInfo_fromRef(v_ref_2575_, v_saveActual_2577_);
                    v___x_2825_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                    v___x_2826_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                    leanh::lean_inc(v___x_2824_);
                    v___x_2827_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2827_, 0, v___x_2824_);
                    leanh::lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                    v___x_2828_ = l_Lean_Syntax_node1(v___x_2824_, v___x_2825_, v___x_2827_);
                    v_actual_2579_ = v___x_2828_;
                    v___y_2580_ = v___x_2823_;
                    v___y_2581_ = v___x_2822_;
                    state = 2;
                    continue;
                } else {
                    v___x_2829_ = 0;
                    v___x_2830_ = l_Lean_SourceInfo_fromRef(v_ref_2575_, v___x_2829_);
                    v___x_2831_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
                    v___x_2832_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34;
                    leanh::lean_inc(v_quotContext_2572_);
                    v___x_2833_ =
                        l_Lean_addMacroScope(v_quotContext_2572_, v___x_2832_, v_macroScope_2565_);
                    v___x_2834_ = leanh::lean_box(0);
                    v___x_2835_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2835_, 0, v___x_2830_);
                    leanh::lean_ctor_set(v___x_2835_, 1, v___x_2831_);
                    leanh::lean_ctor_set(v___x_2835_, 2, v___x_2833_);
                    leanh::lean_ctor_set(v___x_2835_, 3, v___x_2834_);
                    v_actual_2579_ = v___x_2835_;
                    v___y_2580_ = v___x_2823_;
                    v___y_2581_ = v___x_2822_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___boxed(
    mut v_kElse_2838_: *mut leanh::LeanObject,
    mut v_discr_2839_: *mut leanh::LeanObject,
    mut v_alts_2840_: *mut leanh::LeanObject,
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2843_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
        v_kElse_2838_,
        v_discr_2839_,
        v_alts_2840_,
        v_a_2841_,
        v_a_2842_,
    );
    leanh::lean_dec_ref(v_a_2841_);
    return v_res_2843_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(
    mut v_alts_2844_: *mut leanh::LeanObject,
    mut v_discr_2845_: *mut leanh::LeanObject,
    mut v_as_2846_: *mut leanh::LeanObject,
    mut v_as_x27_2847_: *mut leanh::LeanObject,
    mut v_b_2848_: *mut leanh::LeanObject,
    mut v_a_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2852_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2844_, v_discr_2845_, v_as_x27_2847_, v_b_2848_, v___y_2850_, v___y_2851_);
    return v___x_2852_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(
    mut v_alts_2853_: *mut leanh::LeanObject,
    mut v_discr_2854_: *mut leanh::LeanObject,
    mut v_as_2855_: *mut leanh::LeanObject,
    mut v_as_x27_2856_: *mut leanh::LeanObject,
    mut v_b_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v___y_2859_: *mut leanh::LeanObject,
    mut v___y_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2861_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(v_alts_2853_, v_discr_2854_, v_as_2855_, v_as_x27_2856_, v_b_2857_, v_a_2858_, v___y_2859_, v___y_2860_);
    leanh::lean_dec_ref(v___y_2859_);
    leanh::lean_dec(v_as_x27_2856_);
    leanh::lean_dec(v_as_2855_);
    leanh::lean_dec(v_alts_2853_);
    return v_res_2861_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate___lam__0(
    mut v_____do__lift_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
    mut v___y_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = 0;
    v___x_2866_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2862_, v___x_2865_);
    v___x_2867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2867_, 0, v___x_2866_);
    leanh::lean_ctor_set(v___x_2867_, 1, v___y_2864_);
    return v___x_2867_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(
    mut v_____do__lift_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
        v_____do__lift_2868_,
        v___y_2869_,
        v___y_2870_,
    );
    leanh::lean_dec_ref(v___y_2869_);
    leanh::lean_dec(v_____do__lift_2868_);
    return v_res_2871_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
    mut v_as_x27_2878_: *mut leanh::LeanObject,
    mut v_b_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2878_) == 0 {
                    v___x_2882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2882_, 0, v_b_2879_);
                    leanh::lean_ctor_set(v___x_2882_, 1, v___y_2881_);
                    return v___x_2882_;
                } else {
                    v_head_2883_ = leanh::lean_ctor_get(v_as_x27_2878_, 0);
                    v_tail_2884_ = leanh::lean_ctor_get(v_as_x27_2878_, 1);
                    leanh::lean_inc(v_head_2883_);
                    v___x_2885_ = l_Lean_Elab_Term_MatchExpr_getParams(
                        v_head_2883_,
                        v___y_2880_,
                        v___y_2881_,
                    );
                    if leanh::lean_obj_tag(v___x_2885_) == 0 {
                        v_a_2886_ = leanh::lean_ctor_get(v___x_2885_, 0);
                        leanh::lean_inc(v_a_2886_);
                        v_a_2887_ = leanh::lean_ctor_get(v___x_2885_, 1);
                        leanh::lean_inc(v_a_2887_);
                        leanh::lean_dec_ref_known(v___x_2885_, 2);
                        v_ref_2888_ = leanh::lean_ctor_get(v___y_2880_, 5);
                        v___x_2889_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0;
                        v___x_2890_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1;
                        v___x_2891_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                        v_rhs_2892_ = leanh::lean_ctor_get(v_head_2883_, 3);
                        v_k_2893_ = leanh::lean_ctor_get(v_head_2883_, 4);
                        v___x_2894_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                        v___x_2895_ = 0;
                        v___x_2896_ = l_Lean_SourceInfo_fromRef(v_ref_2888_, v___x_2895_);
                        leanh::lean_inc_n(v___x_2896_, 8);
                        v___x_2897_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2897_, 0, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2897_, 1, v___x_2889_);
                        v___x_2898_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                        leanh::lean_inc(v_k_2893_);
                        v___x_2899_ = l_Lean_Syntax_node1(v___x_2896_, v___x_2898_, v_k_2893_);
                        v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                        v___x_2901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                        v___x_2902_ = l_Array_append___redArg(v___x_2901_, v_a_2886_);
                        leanh::lean_dec(v_a_2886_);
                        v___x_2903_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2903_, 0, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2903_, 1, v___x_2900_);
                        leanh::lean_ctor_set(v___x_2903_, 2, v___x_2902_);
                        v___x_2904_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2904_, 0, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2904_, 1, v___x_2900_);
                        leanh::lean_ctor_set(v___x_2904_, 2, v___x_2901_);
                        v___x_2905_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                        v___x_2906_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2906_, 0, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2906_, 1, v___x_2905_);
                        leanh::lean_inc(v_rhs_2892_);
                        v___x_2907_ = l_Lean_Syntax_node5(
                            v___x_2896_,
                            v___x_2894_,
                            v___x_2899_,
                            v___x_2903_,
                            v___x_2904_,
                            v___x_2906_,
                            v_rhs_2892_,
                        );
                        v___x_2908_ = l_Lean_Syntax_node1(v___x_2896_, v___x_2891_, v___x_2907_);
                        v___x_2909_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31;
                        v___x_2910_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2910_, 0, v___x_2896_);
                        leanh::lean_ctor_set(v___x_2910_, 1, v___x_2909_);
                        v___x_2911_ = l_Lean_Syntax_node4(
                            v___x_2896_,
                            v___x_2890_,
                            v___x_2897_,
                            v___x_2908_,
                            v___x_2910_,
                            v_b_2879_,
                        );
                        v_as_x27_2878_ = v_tail_2884_;
                        v_b_2879_ = v___x_2911_;
                        v___y_2881_ = v_a_2887_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_b_2879_);
                        v_a_2913_ = leanh::lean_ctor_get(v___x_2885_, 0);
                        v_a_2914_ = leanh::lean_ctor_get(v___x_2885_, 1);
                        v_isSharedCheck_2921_ =
                            (!leanh::lean_is_exclusive(v___x_2885_)) as u8;
                        if v_isSharedCheck_2921_ == 0 {
                            v___x_2916_ = v___x_2885_;
                            v_isShared_2917_ = v_isSharedCheck_2921_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2914_);
                            leanh::lean_inc(v_a_2913_);
                            leanh::lean_dec(v___x_2885_);
                            v___x_2916_ = leanh::lean_box(0);
                            v_isShared_2917_ = v_isSharedCheck_2921_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2917_ == 0 {
                    v___x_2919_ = v___x_2916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_a_2914_);
                    v___x_2919_ = v_reuseFailAlloc_2920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___boxed(
    mut v_as_x27_2922_: *mut leanh::LeanObject,
    mut v_b_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
    mut v___y_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
        v_as_x27_2922_,
        v_b_2923_,
        v___y_2924_,
        v___y_2925_,
    );
    leanh::lean_dec_ref(v___y_2924_);
    leanh::lean_dec(v_as_x27_2922_);
    return v_res_2926_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
    mut v_x_2927_: *mut leanh::LeanObject,
    mut v_x_2928_: *mut leanh::LeanObject,
    mut v___y_2929_: *mut leanh::LeanObject,
    mut v___y_2930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2927_) == 0 {
                    v___x_2931_ = l_List_reverse___redArg(v_x_2928_);
                    v___x_2932_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2932_, 0, v___x_2931_);
                    leanh::lean_ctor_set(v___x_2932_, 1, v___y_2930_);
                    return v___x_2932_;
                } else {
                    v_head_2933_ = leanh::lean_ctor_get(v_x_2927_, 0);
                    v_tail_2934_ = leanh::lean_ctor_get(v_x_2927_, 1);
                    v_isSharedCheck_2945_ = (!leanh::lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2945_ == 0 {
                        v___x_2936_ = v_x_2927_;
                        v_isShared_2937_ = v_isSharedCheck_2945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2934_);
                        leanh::lean_inc(v_head_2933_);
                        leanh::lean_dec(v_x_2927_);
                        v___x_2936_ = leanh::lean_box(0);
                        v_isShared_2937_ = v_isSharedCheck_2945_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2938_ =
                    l_Lean_Elab_Term_MatchExpr_initK(v_head_2933_, v___y_2929_, v___y_2930_);
                v_a_2939_ = leanh::lean_ctor_get(v___x_2938_, 0);
                leanh::lean_inc(v_a_2939_);
                v_a_2940_ = leanh::lean_ctor_get(v___x_2938_, 1);
                leanh::lean_inc(v_a_2940_);
                leanh::lean_dec_ref(v___x_2938_);
                if v_isShared_2937_ == 0 {
                    leanh::lean_ctor_set(v___x_2936_, 1, v_x_2928_);
                    leanh::lean_ctor_set(v___x_2936_, 0, v_a_2939_);
                    v___x_2942_ = v___x_2936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2944_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_x_2928_);
                    v___x_2942_ = v_reuseFailAlloc_2944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2927_ = v_tail_2934_;
                v_x_2928_ = v___x_2942_;
                v___y_2930_ = v_a_2940_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0___boxed(
    mut v_x_2946_: *mut leanh::LeanObject,
    mut v_x_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
        v_x_2946_,
        v_x_2947_,
        v___y_2948_,
        v___y_2949_,
    );
    leanh::lean_dec_ref(v___y_2948_);
    return v_res_2950_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_Elab_Term_MatchExpr_generate___closed__3;
    v___x_2962_ = l_String_toRawSubstring_x27(v___x_2961_);
    return v___x_2962_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate(
    mut v_discr_2977_: *mut leanh::LeanObject,
    mut v_alts_2978_: *mut leanh::LeanObject,
    mut v_elseAlt_2979_: *mut leanh::LeanObject,
    mut v_a_2980_: *mut leanh::LeanObject,
    mut v_a_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_a_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3091_: u8 = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3095_: u8 = 0;
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_a_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3104_: u8 = 0;
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_a_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2982_ = leanh::lean_box(0);
                v___x_2983_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
                    v_alts_2978_,
                    v___x_2982_,
                    v_a_2980_,
                    v_a_2981_,
                );
                if leanh::lean_obj_tag(v___x_2983_) == 0 {
                    v_a_2984_ = leanh::lean_ctor_get(v___x_2983_, 0);
                    leanh::lean_inc(v_a_2984_);
                    v_a_2985_ = leanh::lean_ctor_get(v___x_2983_, 1);
                    leanh::lean_inc(v_a_2985_);
                    leanh::lean_dec_ref_known(v___x_2983_, 2);
                    v_quotContext_2986_ = leanh::lean_ctor_get(v_a_2980_, 1);
                    v_currMacroScope_2987_ = leanh::lean_ctor_get(v_a_2980_, 2);
                    v_ref_2988_ = leanh::lean_ctor_get(v_a_2980_, 5);
                    v___x_2989_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
                        v_ref_2988_,
                        v_a_2980_,
                        v_a_2985_,
                    );
                    v_a_2990_ = leanh::lean_ctor_get(v___x_2989_, 0);
                    v_a_2991_ = leanh::lean_ctor_get(v___x_2989_, 1);
                    v_isSharedCheck_3110_ = (!leanh::lean_is_exclusive(v___x_2989_)) as u8;
                    if v_isSharedCheck_3110_ == 0 {
                        v___x_2993_ = v___x_2989_;
                        v_isShared_2994_ = v_isSharedCheck_3110_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2991_);
                        leanh::lean_inc(v_a_2990_);
                        leanh::lean_dec(v___x_2989_);
                        v___x_2993_ = leanh::lean_box(0);
                        v_isShared_2994_ = v_isSharedCheck_3110_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_elseAlt_2979_);
                    leanh::lean_dec(v_discr_2977_);
                    v_a_3111_ = leanh::lean_ctor_get(v___x_2983_, 0);
                    v_a_3112_ = leanh::lean_ctor_get(v___x_2983_, 1);
                    v_isSharedCheck_3119_ = (!leanh::lean_is_exclusive(v___x_2983_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3114_ = v___x_2983_;
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3112_);
                        leanh::lean_inc(v_a_3111_);
                        leanh::lean_dec(v___x_2983_);
                        v___x_3114_ = leanh::lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2995_ =
                    l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_2988_, v_a_2980_, v_a_2991_);
                v_a_2996_ = leanh::lean_ctor_get(v___x_2995_, 0);
                v_a_2997_ = leanh::lean_ctor_get(v___x_2995_, 1);
                v_isSharedCheck_3109_ = (!leanh::lean_is_exclusive(v___x_2995_)) as u8;
                if v_isSharedCheck_3109_ == 0 {
                    v___x_2999_ = v___x_2995_;
                    v_isShared_3000_ = v_isSharedCheck_3109_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2997_);
                    leanh::lean_inc(v_a_2996_);
                    leanh::lean_dec(v___x_2995_);
                    v___x_2999_ = leanh::lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
                v___x_3002_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2;
                leanh::lean_inc_n(v_currMacroScope_2987_, 2);
                leanh::lean_inc_n(v_quotContext_2986_, 2);
                v___x_3003_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3002_, v_currMacroScope_2987_);
                leanh::lean_inc(v___x_3003_);
                v___x_3004_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3004_, 0, v_a_2990_);
                leanh::lean_ctor_set(v___x_3004_, 1, v___x_3001_);
                leanh::lean_ctor_set(v___x_3004_, 2, v___x_3003_);
                leanh::lean_ctor_set(v___x_3004_, 3, v___x_2982_);
                v___x_3005_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1_once),
                    _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1,
                );
                v___x_3006_ = l_Lean_Elab_Term_MatchExpr_initK___closed__2;
                v___x_3007_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3006_, v_currMacroScope_2987_);
                leanh::lean_inc(v___x_3007_);
                v___x_3008_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3008_, 0, v_a_2996_);
                leanh::lean_ctor_set(v___x_3008_, 1, v___x_3005_);
                leanh::lean_ctor_set(v___x_3008_, 2, v___x_3007_);
                leanh::lean_ctor_set(v___x_3008_, 3, v___x_2982_);
                leanh::lean_inc(v_a_2984_);
                v___x_3009_ =
                    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
                        v___x_3008_,
                        v___x_3004_,
                        v_a_2984_,
                        v_a_2980_,
                        v_a_2997_,
                    );
                if leanh::lean_obj_tag(v___x_3009_) == 0 {
                    v_a_3010_ = leanh::lean_ctor_get(v___x_3009_, 0);
                    leanh::lean_inc(v_a_3010_);
                    v_a_3011_ = leanh::lean_ctor_get(v___x_3009_, 1);
                    leanh::lean_inc(v_a_3011_);
                    leanh::lean_dec_ref_known(v___x_3009_, 2);
                    v___x_3012_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
                        v_ref_2988_,
                        v_a_2980_,
                        v_a_3011_,
                    );
                    v_a_3013_ = leanh::lean_ctor_get(v___x_3012_, 0);
                    v_a_3014_ = leanh::lean_ctor_get(v___x_3012_, 1);
                    v_isSharedCheck_3099_ = (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3099_ == 0 {
                        v___x_3016_ = v___x_3012_;
                        v_isShared_3017_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3014_);
                        leanh::lean_inc(v_a_3013_);
                        leanh::lean_dec(v___x_3012_);
                        v___x_3016_ = leanh::lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3007_);
                    leanh::lean_dec(v___x_3003_);
                    leanh::lean_del_object(v___x_2999_);
                    leanh::lean_del_object(v___x_2993_);
                    leanh::lean_dec(v_a_2984_);
                    leanh::lean_dec(v_elseAlt_2979_);
                    leanh::lean_dec(v_discr_2977_);
                    v_a_3100_ = leanh::lean_ctor_get(v___x_3009_, 0);
                    v_a_3101_ = leanh::lean_ctor_get(v___x_3009_, 1);
                    v_isSharedCheck_3108_ = (!leanh::lean_is_exclusive(v___x_3009_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v___x_3103_ = v___x_3009_;
                        v_isShared_3104_ = v_isSharedCheck_3108_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3101_);
                        leanh::lean_inc(v_a_3100_);
                        leanh::lean_dec(v___x_3009_);
                        v___x_3103_ = leanh::lean_box(0);
                        v_isShared_3104_ = v_isSharedCheck_3108_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3018_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0;
                v___x_3019_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1;
                leanh::lean_inc(v_a_3013_);
                if v_isShared_3017_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3016_, 2);
                    leanh::lean_ctor_set(v___x_3016_, 1, v___x_3018_);
                    v___x_3021_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3018_);
                    v___x_3021_ = v_reuseFailAlloc_3098_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3022_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_3023_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_3024_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                leanh::lean_inc_n(v_a_3013_, 3);
                v___x_3025_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3025_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3025_, 1, v___x_3005_);
                leanh::lean_ctor_set(v___x_3025_, 2, v___x_3007_);
                leanh::lean_ctor_set(v___x_3025_, 3, v___x_2982_);
                v___x_3026_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3024_, v___x_3025_);
                v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                if v_isShared_3000_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2999_, 2);
                    leanh::lean_ctor_set(v___x_2999_, 1, v___x_3029_);
                    leanh::lean_ctor_set(v___x_2999_, 0, v_a_3013_);
                    v___x_3031_ = v___x_2999_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3032_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                v___x_3033_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                leanh::lean_inc(v_a_3013_);
                if v_isShared_2994_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2993_, 2);
                    leanh::lean_ctor_set(v___x_2993_, 1, v___x_3033_);
                    leanh::lean_ctor_set(v___x_2993_, 0, v_a_3013_);
                    v___x_3035_ = v___x_2993_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_n(v_a_3013_, 23);
                v___x_3036_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3032_, v___x_3035_);
                v___x_3037_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3027_, v___x_3036_);
                v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_3039_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3039_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3039_, 1, v___x_3038_);
                v___x_3040_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2,
                );
                v___x_3041_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__3;
                leanh::lean_inc_n(v_currMacroScope_2987_, 2);
                leanh::lean_inc_n(v_quotContext_2986_, 2);
                v___x_3042_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3041_, v_currMacroScope_2987_);
                v___x_3043_ = l_Lean_Elab_Term_MatchExpr_generate___closed__2;
                v___x_3044_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3044_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3044_, 1, v___x_3040_);
                leanh::lean_ctor_set(v___x_3044_, 2, v___x_3042_);
                leanh::lean_ctor_set(v___x_3044_, 3, v___x_3043_);
                v___x_3045_ = l_Lean_Syntax_node2(v_a_3013_, v___x_3027_, v___x_3039_, v___x_3044_);
                v___x_3046_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_3047_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3047_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3047_, 1, v___x_3027_);
                leanh::lean_ctor_set(v___x_3047_, 2, v___x_3046_);
                v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_3049_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3049_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3049_, 1, v___x_3048_);
                leanh::lean_inc_ref_n(v___x_3047_, 4);
                v___x_3050_ = l_Lean_Syntax_node5(
                    v_a_3013_,
                    v___x_3028_,
                    v___x_3031_,
                    v___x_3037_,
                    v___x_3045_,
                    v___x_3047_,
                    v___x_3049_,
                );
                v___x_3051_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3027_, v___x_3050_);
                v___x_3052_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                v___x_3053_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3053_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3053_, 1, v___x_3052_);
                leanh::lean_inc_ref(v___x_3053_);
                v___x_3054_ = l_Lean_Syntax_node5(
                    v_a_3013_,
                    v___x_3023_,
                    v___x_3026_,
                    v___x_3051_,
                    v___x_3047_,
                    v___x_3053_,
                    v_elseAlt_2979_,
                );
                v___x_3055_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3022_, v___x_3054_);
                v___x_3056_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31;
                v___x_3057_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3057_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3057_, 1, v___x_3056_);
                v___x_3058_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_3059_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_3060_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3060_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3060_, 1, v___x_3058_);
                v___x_3061_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_3062_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3061_, v___x_3047_);
                v___x_3063_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3063_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3063_, 1, v___x_3001_);
                leanh::lean_ctor_set(v___x_3063_, 2, v___x_3003_);
                leanh::lean_ctor_set(v___x_3063_, 3, v___x_2982_);
                v___x_3064_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3024_, v___x_3063_);
                v___x_3065_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_3066_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_generate___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_generate___closed__4_once),
                    _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4,
                );
                v___x_3067_ = l_Lean_Elab_Term_MatchExpr_generate___closed__6;
                v___x_3068_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3067_, v_currMacroScope_2987_);
                v___x_3069_ = l_Lean_Elab_Term_MatchExpr_generate___closed__9;
                v___x_3070_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3070_, 0, v_a_3013_);
                leanh::lean_ctor_set(v___x_3070_, 1, v___x_3066_);
                leanh::lean_ctor_set(v___x_3070_, 2, v___x_3068_);
                leanh::lean_ctor_set(v___x_3070_, 3, v___x_3069_);
                v___x_3071_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3027_, v_discr_2977_);
                v___x_3072_ = l_Lean_Syntax_node2(v_a_3013_, v___x_3065_, v___x_3070_, v___x_3071_);
                v___x_3073_ = l_Lean_Syntax_node5(
                    v_a_3013_,
                    v___x_3023_,
                    v___x_3064_,
                    v___x_3047_,
                    v___x_3047_,
                    v___x_3053_,
                    v___x_3072_,
                );
                v___x_3074_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3022_, v___x_3073_);
                leanh::lean_inc_ref(v___x_3057_);
                v___x_3075_ = l_Lean_Syntax_node5(
                    v_a_3013_,
                    v___x_3059_,
                    v___x_3060_,
                    v___x_3062_,
                    v___x_3074_,
                    v___x_3057_,
                    v_a_3010_,
                );
                v___x_3076_ = l_Lean_Syntax_node4(
                    v_a_3013_,
                    v___x_3019_,
                    v___x_3021_,
                    v___x_3055_,
                    v___x_3057_,
                    v___x_3075_,
                );
                v___x_3077_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(v_a_2984_, v___x_3076_, v_a_2980_, v_a_3014_);
                leanh::lean_dec(v_a_2984_);
                if leanh::lean_obj_tag(v___x_3077_) == 0 {
                    v_a_3078_ = leanh::lean_ctor_get(v___x_3077_, 0);
                    v_a_3079_ = leanh::lean_ctor_get(v___x_3077_, 1);
                    v_isSharedCheck_3086_ = (!leanh::lean_is_exclusive(v___x_3077_)) as u8;
                    if v_isSharedCheck_3086_ == 0 {
                        v___x_3081_ = v___x_3077_;
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3079_);
                        leanh::lean_inc(v_a_3078_);
                        leanh::lean_dec(v___x_3077_);
                        v___x_3081_ = leanh::lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_3087_ = leanh::lean_ctor_get(v___x_3077_, 0);
                    v_a_3088_ = leanh::lean_ctor_get(v___x_3077_, 1);
                    v_isSharedCheck_3095_ = (!leanh::lean_is_exclusive(v___x_3077_)) as u8;
                    if v_isSharedCheck_3095_ == 0 {
                        v___x_3090_ = v___x_3077_;
                        v_isShared_3091_ = v_isSharedCheck_3095_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3088_);
                        leanh::lean_inc(v_a_3087_);
                        leanh::lean_dec(v___x_3077_);
                        v___x_3090_ = leanh::lean_box(0);
                        v_isShared_3091_ = v_isSharedCheck_3095_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3084_;
            }
            9 => {
                if v_isShared_3091_ == 0 {
                    v___x_3093_ = v___x_3090_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3094_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3088_);
                    v___x_3093_ = v_reuseFailAlloc_3094_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3093_;
            }
            11 => {
                if v_isShared_3104_ == 0 {
                    v___x_3106_ = v___x_3103_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3107_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_a_3101_);
                    v___x_3106_ = v_reuseFailAlloc_3107_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3106_;
            }
            13 => {
                if v_isShared_3115_ == 0 {
                    v___x_3117_ = v___x_3114_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3111_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_a_3112_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate___boxed(
    mut v_discr_3120_: *mut leanh::LeanObject,
    mut v_alts_3121_: *mut leanh::LeanObject,
    mut v_elseAlt_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Lean_Elab_Term_MatchExpr_generate(
        v_discr_3120_,
        v_alts_3121_,
        v_elseAlt_3122_,
        v_a_3123_,
        v_a_3124_,
    );
    leanh::lean_dec_ref(v_a_3123_);
    return v_res_3125_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(
    mut v_as_3126_: *mut leanh::LeanObject,
    mut v_as_x27_3127_: *mut leanh::LeanObject,
    mut v_b_3128_: *mut leanh::LeanObject,
    mut v_a_3129_: *mut leanh::LeanObject,
    mut v___y_3130_: *mut leanh::LeanObject,
    mut v___y_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
        v_as_x27_3127_,
        v_b_3128_,
        v___y_3130_,
        v___y_3131_,
    );
    return v___x_3132_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(
    mut v_as_3133_: *mut leanh::LeanObject,
    mut v_as_x27_3134_: *mut leanh::LeanObject,
    mut v_b_3135_: *mut leanh::LeanObject,
    mut v_a_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(
        v_as_3133_,
        v_as_x27_3134_,
        v_b_3135_,
        v_a_3136_,
        v___y_3137_,
        v___y_3138_,
    );
    leanh::lean_dec_ref(v___y_3137_);
    leanh::lean_dec(v_as_x27_3134_);
    leanh::lean_dec(v_as_3133_);
    return v_res_3139_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
    mut v_x_3141_: *mut leanh::LeanObject,
    mut v_x_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v_a_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3141_) == 0 {
                    v___x_3145_ = l_List_reverse___redArg(v_x_3142_);
                    v___x_3146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3146_, 0, v___x_3145_);
                    leanh::lean_ctor_set(v___x_3146_, 1, v___y_3144_);
                    return v___x_3146_;
                } else {
                    v_head_3147_ = leanh::lean_ctor_get(v_x_3141_, 0);
                    v_tail_3148_ = leanh::lean_ctor_get(v_x_3141_, 1);
                    v_isSharedCheck_3174_ = (!leanh::lean_is_exclusive(v_x_3141_)) as u8;
                    if v_isSharedCheck_3174_ == 0 {
                        v___x_3150_ = v_x_3141_;
                        v_isShared_3151_ = v_isSharedCheck_3174_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3148_);
                        leanh::lean_inc(v_head_3147_);
                        leanh::lean_dec(v_x_3141_);
                        v___x_3150_ = leanh::lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3174_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_head_3147_);
                v___x_3159_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(v_head_3147_);
                if leanh::lean_obj_tag(v___x_3159_) == 1 {
                    leanh::lean_dec(v_head_3147_);
                    v_val_3160_ = leanh::lean_ctor_get(v___x_3159_, 0);
                    leanh::lean_inc(v_val_3160_);
                    leanh::lean_dec_ref_known(v___x_3159_, 1);
                    v_a_3153_ = v_val_3160_;
                    v_a_3154_ = v___y_3144_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3159_);
                    v___x_3161_ =
                        l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0;
                    v___x_3162_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_head_3147_,
                        v___x_3161_,
                        v___y_3143_,
                        v___y_3144_,
                    );
                    leanh::lean_dec(v_head_3147_);
                    if leanh::lean_obj_tag(v___x_3162_) == 0 {
                        v_a_3163_ = leanh::lean_ctor_get(v___x_3162_, 0);
                        leanh::lean_inc(v_a_3163_);
                        v_a_3164_ = leanh::lean_ctor_get(v___x_3162_, 1);
                        leanh::lean_inc(v_a_3164_);
                        leanh::lean_dec_ref_known(v___x_3162_, 2);
                        v_a_3153_ = v_a_3163_;
                        v_a_3154_ = v_a_3164_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3150_);
                        leanh::lean_dec(v_tail_3148_);
                        leanh::lean_dec(v_x_3142_);
                        v_a_3165_ = leanh::lean_ctor_get(v___x_3162_, 0);
                        v_a_3166_ = leanh::lean_ctor_get(v___x_3162_, 1);
                        v_isSharedCheck_3173_ =
                            (!leanh::lean_is_exclusive(v___x_3162_)) as u8;
                        if v_isSharedCheck_3173_ == 0 {
                            v___x_3168_ = v___x_3162_;
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3166_);
                            leanh::lean_inc(v_a_3165_);
                            leanh::lean_dec(v___x_3162_);
                            v___x_3168_ = leanh::lean_box(0);
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_3151_ == 0 {
                    leanh::lean_ctor_set(v___x_3150_, 1, v_x_3142_);
                    leanh::lean_ctor_set(v___x_3150_, 0, v_a_3153_);
                    v___x_3156_ = v___x_3150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_x_3142_);
                    v___x_3156_ = v_reuseFailAlloc_3158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_3141_ = v_tail_3148_;
                v_x_3142_ = v___x_3156_;
                v___y_3144_ = v_a_3154_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3169_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3166_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___boxed(
    mut v_x_3175_: *mut leanh::LeanObject,
    mut v_x_3176_: *mut leanh::LeanObject,
    mut v___y_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
        v_x_3175_,
        v_x_3176_,
        v___y_3177_,
        v___y_3178_,
    );
    leanh::lean_dec_ref(v___y_3177_);
    return v_res_3179_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_main(
    mut v_discr_3181_: *mut leanh::LeanObject,
    mut v_alts_3182_: *mut leanh::LeanObject,
    mut v_elseAlt_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
    mut v_a_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3186_ = lean_array_to_list(v_alts_3182_);
                v___x_3187_ = leanh::lean_box(0);
                v___x_3188_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
                    v___x_3186_,
                    v___x_3187_,
                    v_a_3184_,
                    v_a_3185_,
                );
                if leanh::lean_obj_tag(v___x_3188_) == 0 {
                    v_a_3189_ = leanh::lean_ctor_get(v___x_3188_, 0);
                    leanh::lean_inc(v_a_3189_);
                    v_a_3190_ = leanh::lean_ctor_get(v___x_3188_, 1);
                    leanh::lean_inc(v_a_3190_);
                    leanh::lean_dec_ref_known(v___x_3188_, 2);
                    leanh::lean_inc(v_elseAlt_3183_);
                    v___x_3191_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(v_elseAlt_3183_);
                    if leanh::lean_obj_tag(v___x_3191_) == 1 {
                        leanh::lean_dec(v_elseAlt_3183_);
                        v_val_3192_ = leanh::lean_ctor_get(v___x_3191_, 0);
                        leanh::lean_inc(v_val_3192_);
                        leanh::lean_dec_ref_known(v___x_3191_, 1);
                        v___x_3193_ = l_Lean_Elab_Term_MatchExpr_generate(
                            v_discr_3181_,
                            v_a_3189_,
                            v_val_3192_,
                            v_a_3184_,
                            v_a_3190_,
                        );
                        return v___x_3193_;
                    } else {
                        leanh::lean_dec(v___x_3191_);
                        leanh::lean_dec(v_a_3189_);
                        leanh::lean_dec(v_discr_3181_);
                        v___x_3194_ = l_Lean_Elab_Term_MatchExpr_main___closed__0;
                        v___x_3195_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_elseAlt_3183_,
                            v___x_3194_,
                            v_a_3184_,
                            v_a_3190_,
                        );
                        leanh::lean_dec(v_elseAlt_3183_);
                        return v___x_3195_;
                    }
                } else {
                    leanh::lean_dec(v_elseAlt_3183_);
                    leanh::lean_dec(v_discr_3181_);
                    v_a_3196_ = leanh::lean_ctor_get(v___x_3188_, 0);
                    v_a_3197_ = leanh::lean_ctor_get(v___x_3188_, 1);
                    v_isSharedCheck_3204_ = (!leanh::lean_is_exclusive(v___x_3188_)) as u8;
                    if v_isSharedCheck_3204_ == 0 {
                        v___x_3199_ = v___x_3188_;
                        v_isShared_3200_ = v_isSharedCheck_3204_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3197_);
                        leanh::lean_inc(v_a_3196_);
                        leanh::lean_dec(v___x_3188_);
                        v___x_3199_ = leanh::lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3204_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3200_ == 0 {
                    v___x_3202_ = v___x_3199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_a_3197_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_main___boxed(
    mut v_discr_3205_: *mut leanh::LeanObject,
    mut v_alts_3206_: *mut leanh::LeanObject,
    mut v_elseAlt_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
    mut v_a_3209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3210_ = l_Lean_Elab_Term_MatchExpr_main(
        v_discr_3205_,
        v_alts_3206_,
        v_elseAlt_3207_,
        v_a_3208_,
        v_a_3209_,
    );
    leanh::lean_dec_ref(v_a_3208_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_Elab_Term_expandMatchExpr(
    mut v_stx_3217_: *mut leanh::LeanObject,
    mut v_a_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: u8 = 0;
    v___x_3220_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
    leanh::lean_inc(v_stx_3217_);
    v___x_3221_ = l_Lean_Syntax_isOfKind(v_stx_3217_, v___x_3220_);
    if v___x_3221_ == 0 {
        let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_3217_);
        v___x_3222_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3219_);
        return v___x_3222_;
    } else {
        let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_discr_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3223_ = leanh::lean_unsigned_to_nat(0);
        v___x_3224_ = leanh::lean_unsigned_to_nat(1);
        v_discr_3225_ = l_Lean_Syntax_getArg(v_stx_3217_, v___x_3224_);
        v___x_3226_ = leanh::lean_unsigned_to_nat(3);
        v___x_3227_ = l_Lean_Syntax_getArg(v_stx_3217_, v___x_3226_);
        leanh::lean_dec(v_stx_3217_);
        v___x_3228_ = l_Lean_Syntax_getArg(v___x_3227_, v___x_3223_);
        v___x_3229_ = l_Lean_Syntax_getArgs(v___x_3228_);
        leanh::lean_dec(v___x_3228_);
        v___x_3230_ = l_Lean_Syntax_getArg(v___x_3227_, v___x_3224_);
        leanh::lean_dec(v___x_3227_);
        v___x_3231_ = l_Lean_Elab_Term_MatchExpr_main(
            v_discr_3225_,
            v___x_3229_,
            v___x_3230_,
            v_a_3218_,
            v_a_3219_,
        );
        return v___x_3231_;
    }
}
pub unsafe fn l_Lean_Elab_Term_expandMatchExpr___boxed(
    mut v_stx_3232_: *mut leanh::LeanObject,
    mut v_a_3233_: *mut leanh::LeanObject,
    mut v_a_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_Elab_Term_expandMatchExpr(v_stx_3232_, v_a_3233_, v_a_3234_);
    leanh::lean_dec_ref(v_a_3233_);
    return v_res_3235_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1()
-> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_Elab_macroAttribute;
    v___x_3244_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
    v___x_3245_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1;
    v___x_3246_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandMatchExpr___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_3247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3243_,
        v___x_3244_,
        v___x_3245_,
        v___x_3246_,
    );
    return v___x_3247_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___boxed(
    mut v_a_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
    return v_res_3249_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3276_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1;
    v___x_3277_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6;
    v___x_3278_ = l_Lean_addBuiltinDeclarationRanges(v___x_3276_, v___x_3277_);
    return v___x_3278_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(
    mut v_a_3279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3280_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
    return v_res_3280_;
}
pub unsafe fn l_Lean_Elab_Term_expandLetExpr(
    mut v_stx_3297_: *mut leanh::LeanObject,
    mut v_a_3298_: *mut leanh::LeanObject,
    mut v_a_3299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: u8 = 0;
    v___x_3300_ = l_Lean_Elab_Term_expandLetExpr___closed__1;
    leanh::lean_inc(v_stx_3297_);
    v___x_3301_ = l_Lean_Syntax_isOfKind(v_stx_3297_, v___x_3300_);
    if v___x_3301_ == 0 {
        let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_3297_);
        v___x_3302_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3299_);
        return v___x_3302_;
    } else {
        let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3306_: u8 = 0;
        v___x_3303_ = leanh::lean_unsigned_to_nat(1);
        v___x_3304_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3303_);
        v___x_3305_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5;
        leanh::lean_inc(v___x_3304_);
        v___x_3306_ = l_Lean_Syntax_isOfKind(v___x_3304_, v___x_3305_);
        if v___x_3306_ == 0 {
            let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_3304_);
            leanh::lean_dec(v_stx_3297_);
            v___x_3307_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3299_);
            return v___x_3307_;
        } else {
            let mut v_ref_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3315_: u8 = 0;
            let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_3308_ = leanh::lean_ctor_get(v_a_3298_, 5);
            v___x_3309_ = leanh::lean_unsigned_to_nat(3);
            v___x_3310_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3309_);
            v___x_3311_ = leanh::lean_unsigned_to_nat(5);
            v___x_3312_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3311_);
            v___x_3313_ = leanh::lean_unsigned_to_nat(7);
            v___x_3314_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3313_);
            leanh::lean_dec(v_stx_3297_);
            v___x_3315_ = 0;
            v___x_3316_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v___x_3315_);
            v___x_3317_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
            v___x_3318_ = l_Lean_Elab_Term_expandLetExpr___closed__2;
            leanh::lean_inc_n(v___x_3316_, 10);
            v___x_3319_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3319_, 0, v___x_3316_);
            leanh::lean_ctor_set(v___x_3319_, 1, v___x_3318_);
            v___x_3320_ = l_Lean_Elab_Term_expandLetExpr___closed__3;
            v___x_3321_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3321_, 0, v___x_3316_);
            leanh::lean_ctor_set(v___x_3321_, 1, v___x_3320_);
            v___x_3322_ = l_Lean_Elab_Term_expandLetExpr___closed__5;
            v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
            v___x_3324_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1;
            v___x_3325_ = l_Lean_Elab_Term_expandLetExpr___closed__6;
            v___x_3326_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3326_, 0, v___x_3316_);
            leanh::lean_ctor_set(v___x_3326_, 1, v___x_3325_);
            v___x_3327_ = l_Lean_Elab_Term_expandLetExpr___closed__7;
            v___x_3328_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3328_, 0, v___x_3316_);
            leanh::lean_ctor_set(v___x_3328_, 1, v___x_3327_);
            leanh::lean_inc_ref(v___x_3328_);
            leanh::lean_inc_ref(v___x_3326_);
            v___x_3329_ = l_Lean_Syntax_node4(
                v___x_3316_,
                v___x_3324_,
                v___x_3326_,
                v___x_3304_,
                v___x_3328_,
                v___x_3314_,
            );
            v___x_3330_ = l_Lean_Syntax_node1(v___x_3316_, v___x_3323_, v___x_3329_);
            v___x_3331_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4;
            v___x_3332_ =
                l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
            v___x_3333_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
            v___x_3334_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3334_, 0, v___x_3316_);
            leanh::lean_ctor_set(v___x_3334_, 1, v___x_3333_);
            v___x_3335_ = l_Lean_Syntax_node1(v___x_3316_, v___x_3332_, v___x_3334_);
            v___x_3336_ = l_Lean_Syntax_node4(
                v___x_3316_,
                v___x_3331_,
                v___x_3326_,
                v___x_3335_,
                v___x_3328_,
                v___x_3312_,
            );
            v___x_3337_ = l_Lean_Syntax_node2(v___x_3316_, v___x_3322_, v___x_3330_, v___x_3336_);
            v___x_3338_ = l_Lean_Syntax_node4(
                v___x_3316_,
                v___x_3317_,
                v___x_3319_,
                v___x_3310_,
                v___x_3321_,
                v___x_3337_,
            );
            v___x_3339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3339_, 0, v___x_3338_);
            leanh::lean_ctor_set(v___x_3339_, 1, v_a_3299_);
            return v___x_3339_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandLetExpr___boxed(
    mut v_stx_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Lean_Elab_Term_expandLetExpr(v_stx_3340_, v_a_3341_, v_a_3342_);
    leanh::lean_dec_ref(v_a_3341_);
    return v_res_3343_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1()
-> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Lean_Elab_macroAttribute;
    v___x_3352_ = l_Lean_Elab_Term_expandLetExpr___closed__1;
    v___x_3353_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1;
    v___x_3354_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Term_expandLetExpr___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_3355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3351_,
        v___x_3352_,
        v___x_3353_,
        v___x_3354_,
    );
    return v___x_3355_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___boxed(
    mut v_a_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3384_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1;
    v___x_3385_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6;
    v___x_3386_ = l_Lean_addBuiltinDeclarationRanges(v___x_3384_, v___x_3385_);
    return v___x_3386_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(
    mut v_a_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
    return v_res_3388_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MatchExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MatchExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_MatchExpr(builtin);
}
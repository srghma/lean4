// Lean compiler output
// Module: Lean.Elab.MatchExpr
// Imports: Lean.Elab.Term
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwErrorAt___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value: LeanStringObject<17> =
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
            109, 97, 116, 99, 104, 69, 120, 112, 114, 69, 108, 115, 101, 65, 108, 116, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__3_value)
                as *mut LeanObject,
            1632499211127915769 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value
) as *mut LeanObject;
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__0_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__0_value)
                as *mut LeanObject,
            4415435816164107676 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__2_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__4_value)
                as *mut LeanObject,
            2538307196702464034 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_next___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Term_MatchExpr_next___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_next___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_initK___closed__0_value: LeanStringObject<8> =
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
        m_data: [95, 95, 100, 111, 95, 106, 112, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_initK___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__0_value) as *mut LeanObject,
        15820227558662830522 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_MatchExpr_initK___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_initK___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__0_value) as *mut LeanObject,17201320286889277233 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__3_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 120, 112, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5816915816860015341 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5933584171502587988 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__9_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__12_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value: LeanStringObject<5> =
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
        m_data: [85, 110, 105, 116, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__1_value)
                as *mut LeanObject,
            9833841078580172006 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getParams___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value: LeanStringObject<6> =
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
        m_data: [116, 117, 112, 108, 101, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__0_value)
                as *mut LeanObject,
            15644373471618144447 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value: LeanStringObject<15> =
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
            104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__2_value)
                as *mut LeanObject,
            7306243862518720553 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value: LeanStringObject<12> =
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
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__4_value)
                as *mut LeanObject,
            9871775667037945883 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value: LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            7892421401833366012 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__9_value)
                as *mut LeanObject,
            3118387575542340883 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            7892421401833366012 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__17_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_getActuals___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value: LeanStringObject<17> =
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
            100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__0_value)
                as *mut LeanObject,
            11323065835382012354 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__3_value) as *mut LeanObject,5353940006376281447 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__5_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 115, 67, 111, 110, 115, 116, 79, 102, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8_value) as *mut LeanObject,10912452762630170651 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__11_value) as *mut LeanObject,14296711813398647265 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 95, 100, 105, 115, 99, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0_value) as *mut LeanObject,16733771387975461799 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 101, 114, 109, 68, 101, 112, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__3_value) as *mut LeanObject,12532511233276993215 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value
) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__5_value) as *mut LeanObject,13771926289831477797 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 115, 65, 112, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10_value) as *mut LeanObject,15267956672266940778 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13_value) as *mut LeanObject,146480343229376155 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__15_value) as *mut LeanObject,17404204824591055365 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__17_value) as *mut LeanObject,8036185514257755965 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__19_value) as *mut LeanObject,17116161260408496210 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__21_value) as *mut LeanObject,13708106407786339395 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [69, 120, 112, 114, 46, 97, 112, 112, 70, 110, 67, 108, 101, 97, 110, 117, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24_value) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 112, 112, 70, 110, 67, 108, 101, 97, 110, 117, 112, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5816915816860015341 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut LeanObject,2608827092792194939 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5933584171502587988 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__26_value) as *mut LeanObject,8323309418843702446 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__28_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__29_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__31_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32_value) as *mut LeanObject,7839396180116328695 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 112, 114, 46, 97, 112, 112, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35_value) as *mut LeanObject;
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 65, 114, 103, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5816915816860015341 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut LeanObject,14289070523719690127 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5933584171502587988 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__37_value) as *mut LeanObject,7686834297966724978 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__39_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__40_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 116, 95, 100, 101, 108, 97, 121, 101, 100, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0_value) as *mut LeanObject,18341947624523515681 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__0_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__3_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getParams___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__3_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            69, 120, 112, 114, 46, 99, 108, 101, 97, 110, 117, 112, 65, 110, 110, 111, 116, 97,
            116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__5_value: LeanStringObject<19> =
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
            99, 108, 101, 97, 110, 117, 112, 65, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5816915816860015341 as *mut LeanObject] };
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value)
                as *mut LeanObject,
            8192533573043082760 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__6_value) as *mut LeanObject;
static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6_value) as *mut LeanObject,5933584171502587988 as *mut LeanObject] };
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__5_value)
                as *mut LeanObject,
            4039834411699617061 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_generate___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__8_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Term_MatchExpr_generate___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_generate___closed__9_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value:
    LeanStringObject<36> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Term_MatchExpr_main___closed__0_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_MatchExpr_main___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_main___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandMatchExpr___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_expandMatchExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Term_expandMatchExpr___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__0_value) as *mut LeanObject,
        6386943139076865352 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_expandMatchExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandMatchExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 120, 112, 97, 110, 100, 77, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__0_value) as *mut LeanObject,17839991279989882916 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 207 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__0_value) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 203 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__3_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__4_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__0_value: LeanStringObject<8> =
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
        m_data: [108, 101, 116, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Term_expandLetExpr___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__0_value) as *mut LeanObject,
        9932332765764045546 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_expandLetExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__2_value: LeanStringObject<11> =
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
        m_data: [109, 97, 116, 99, 104, 95, 101, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__3_value: LeanStringObject<5> =
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
        m_data: [119, 105, 116, 104, 0],
    };
static mut l_Lean_Elab_Term_expandLetExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__4_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_expandLetExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Term_expandLetExpr___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__4_value) as *mut LeanObject,
        13500049350435642968 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Term_expandLetExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__6_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_expandLetExpr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Term_expandLetExpr___closed__7_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Term_expandLetExpr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_expandLetExpr___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 112, 97, 110, 100, 76, 101, 116, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__8_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__2_value) as *mut LeanObject,7892421401833366012 as *mut LeanObject] };
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__0_value) as *mut LeanObject,6927429308684558226 as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 215 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__0_value) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 209 as usize) << 1) | 1) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__3_value) as *mut LeanObject,((( 46 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__4_value) as *mut LeanObject,((( 59 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(
    mut v_stx_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    v___x_1705_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f___closed__4;
    lean_inc(v_stx_1704_);
    v___x_1706_ = l_Lean_Syntax_isOfKind(v_stx_1704_, v___x_1705_);
    if v___x_1706_ == 0 {
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_1704_);
        v___x_1707_ = lean_box(0);
        return v___x_1707_;
    } else {
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
        v___x_1708_ = lean_unsigned_to_nat(3);
        v___x_1709_ = l_Lean_Syntax_getArg(v_stx_1704_, v___x_1708_);
        lean_dec(v_stx_1704_);
        v___x_1710_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1710_, 0, v___x_1709_);
        return v___x_1710_;
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1717_) == 0 {
                    v___x_1719_ = l_List_reverse___redArg(v_a_1718_);
                    return v___x_1719_;
                } else {
                    v_head_1720_ = lean_ctor_get(v_a_1717_, 0);
                    v_tail_1721_ = lean_ctor_get(v_a_1717_, 1);
                    v_isSharedCheck_1735_ = (!lean_is_exclusive(v_a_1717_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1723_ = v_a_1717_;
                        v_isShared_1724_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1721_);
                        lean_inc(v_head_1720_);
                        lean_dec(v_a_1717_);
                        v___x_1723_ = lean_box(0);
                        v_isShared_1724_ = v_isSharedCheck_1735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1731_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                lean_inc(v_head_1720_);
                v___x_1732_ = l_Lean_Syntax_isOfKind(v_head_1720_, v___x_1731_);
                if v___x_1732_ == 0 {
                    v___x_1733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1733_, 0, v_head_1720_);
                    v___y_1726_ = v___x_1733_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_head_1720_);
                    v___x_1734_ = lean_box(0);
                    v___y_1726_ = v___x_1734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1724_ == 0 {
                    lean_ctor_set(v___x_1723_, 1, v_a_1718_);
                    lean_ctor_set(v___x_1723_, 0, v___y_1726_);
                    v___x_1728_ = v___x_1723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___y_1726_);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1718_);
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
    mut v_stx_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1752_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1;
                lean_inc(v_stx_1751_);
                v___x_1753_ = l_Lean_Syntax_isOfKind(v_stx_1751_, v___x_1752_);
                if v___x_1753_ == 0 {
                    lean_dec(v_stx_1751_);
                    v___x_1754_ = lean_box(0);
                    return v___x_1754_;
                } else {
                    v___x_1755_ = lean_unsigned_to_nat(1);
                    v___x_1756_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1755_);
                    v___x_1775_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5;
                    lean_inc(v___x_1756_);
                    v___x_1776_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1775_);
                    if v___x_1776_ == 0 {
                        lean_dec(v___x_1756_);
                        lean_dec(v_stx_1751_);
                        v___x_1777_ = lean_box(0);
                        return v___x_1777_;
                    } else {
                        v___x_1778_ = lean_unsigned_to_nat(0);
                        v___x_1779_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1778_);
                        v___x_1780_ = l_Lean_Syntax_isNone(v___x_1779_);
                        if v___x_1780_ == 0 {
                            v___x_1781_ = lean_unsigned_to_nat(2);
                            lean_inc(v___x_1779_);
                            v___x_1782_ = l_Lean_Syntax_matchesNull(v___x_1779_, v___x_1781_);
                            if v___x_1782_ == 0 {
                                lean_dec(v___x_1779_);
                                lean_dec(v___x_1756_);
                                lean_dec(v_stx_1751_);
                                v___x_1783_ = lean_box(0);
                                return v___x_1783_;
                            } else {
                                v_var_x3f_1784_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1778_);
                                lean_dec(v___x_1779_);
                                v___x_1785_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1785_, 0, v_var_x3f_1784_);
                                v_var_x3f_1758_ = v___x_1785_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1779_);
                            v___x_1786_ = lean_box(0);
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
                lean_inc(v_funName_1759_);
                v___x_1761_ = l_Lean_Syntax_isOfKind(v_funName_1759_, v___x_1760_);
                if v___x_1761_ == 0 {
                    lean_dec(v_funName_1759_);
                    lean_dec(v_var_x3f_1758_);
                    lean_dec(v___x_1756_);
                    lean_dec(v_stx_1751_);
                    v___x_1762_ = lean_box(0);
                    return v___x_1762_;
                } else {
                    v___x_1763_ = lean_unsigned_to_nat(2);
                    v___x_1764_ = l_Lean_Syntax_getArg(v___x_1756_, v___x_1763_);
                    lean_dec(v___x_1756_);
                    v_pvars_1765_ = l_Lean_Syntax_getArgs(v___x_1764_);
                    lean_dec(v___x_1764_);
                    v___x_1766_ = lean_array_to_list(v_pvars_1765_);
                    v___x_1767_ = l_List_reverse___redArg(v___x_1766_);
                    v___x_1768_ = lean_box(0);
                    v_pvars_1769_ =
                        l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0(
                            v___x_1767_,
                            v___x_1768_,
                        );
                    v___x_1770_ = lean_unsigned_to_nat(3);
                    v_rhs_1771_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1770_);
                    lean_dec(v_stx_1751_);
                    v___x_1772_ = lean_box(0);
                    v___x_1773_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v___x_1773_, 0, v_var_x3f_1758_);
                    lean_ctor_set(v___x_1773_, 1, v_funName_1759_);
                    lean_ctor_set(v___x_1773_, 2, v_pvars_1769_);
                    lean_ctor_set(v___x_1773_, 3, v_rhs_1771_);
                    lean_ctor_set(v___x_1773_, 4, v___x_1772_);
                    lean_ctor_set(v___x_1773_, 5, v___x_1768_);
                    v___x_1774_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1774_, 0, v___x_1773_);
                    return v___x_1774_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(
    mut v_a_1790_: *mut LeanObject,
    mut v_as_1791_: *mut LeanObject,
    mut v_sz_1792_: usize,
    mut v_i_1793_: usize,
    mut v_b_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: u8 = 0;
    let mut v_funName_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: usize = 0;
    let mut v___x_1804_: usize = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1795_ = lean_usize_dec_lt(v_i_1793_, v_sz_1792_);
                if v___x_1795_ == 0 {
                    lean_inc_ref(v_b_1794_);
                    return v_b_1794_;
                } else {
                    v_funName_1796_ = lean_ctor_get(v_a_1790_, 1);
                    v___x_1797_ = lean_box(0);
                    v_a_1798_ = lean_array_uget_borrowed(v_as_1791_, v_i_1793_);
                    v___x_1799_ = l_Lean_TSyntax_getId(v_a_1798_);
                    v___x_1800_ = l_Lean_TSyntax_getId(v_funName_1796_);
                    v___x_1801_ = lean_name_eq(v___x_1799_, v___x_1800_);
                    lean_dec(v___x_1800_);
                    lean_dec(v___x_1799_);
                    if v___x_1801_ == 0 {
                        v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___closed__0;
                        v___x_1803_ = 1usize;
                        v___x_1804_ = lean_usize_add(v_i_1793_, v___x_1803_);
                        v_i_1793_ = v___x_1804_;
                        v_b_1794_ = v___x_1802_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_a_1798_);
                        v___x_1806_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1806_, 0, v_a_1798_);
                        v___x_1807_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1807_, 0, v___x_1806_);
                        v___x_1808_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1808_, 0, v___x_1807_);
                        lean_ctor_set(v___x_1808_, 1, v___x_1797_);
                        return v___x_1808_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0___boxed(
    mut v_a_1809_: *mut LeanObject,
    mut v_as_1810_: *mut LeanObject,
    mut v_sz_1811_: *mut LeanObject,
    mut v_i_1812_: *mut LeanObject,
    mut v_b_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1814_: usize = 0;
    let mut v_i_boxed_1815_: usize = 0;
    let mut v_res_1816_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1814_ = lean_unbox_usize(v_sz_1811_);
    lean_dec(v_sz_1811_);
    v_i_boxed_1815_ = lean_unbox_usize(v_i_1812_);
    lean_dec(v_i_1812_);
    v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__0(v_a_1809_, v_as_1810_, v_sz_boxed_1814_, v_i_boxed_1815_, v_b_1813_);
    lean_dec_ref(v_b_1813_);
    lean_dec_ref(v_as_1810_);
    lean_dec_ref(v_a_1809_);
    return v_res_1816_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
    mut v_as_x27_1817_: *mut LeanObject,
    mut v_b_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1830_: usize = 0;
    let mut v___x_1831_: usize = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1817_) == 0 {
                    return v_b_1818_;
                } else {
                    v_head_1819_ = lean_ctor_get(v_as_x27_1817_, 0);
                    v_tail_1820_ = lean_ctor_get(v_as_x27_1817_, 1);
                    v_funName_1821_ = lean_ctor_get(v_head_1819_, 1);
                    v_pvars_1822_ = lean_ctor_get(v_head_1819_, 2);
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
                        v_fst_1833_ = lean_ctor_get(v___x_1832_, 0);
                        lean_inc(v_fst_1833_);
                        lean_dec_ref(v___x_1832_);
                        if lean_obj_tag(v_fst_1833_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_val_1834_ = lean_ctor_get(v_fst_1833_, 0);
                            lean_inc(v_val_1834_);
                            lean_dec_ref_known(v_fst_1833_, 1);
                            if lean_obj_tag(v_val_1834_) == 0 {
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v_val_1834_, 1);
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
                    lean_inc(v_funName_1821_);
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
    mut v_as_x27_1836_: *mut LeanObject,
    mut v_b_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1838_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
            v_as_x27_1836_,
            v_b_1837_,
        );
    lean_dec(v_as_x27_1836_);
    return v_res_1838_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(
    mut v_alts_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_funNames_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_alts_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_1845_);
    lean_dec(v_alts_1845_);
    return v_res_1846_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(
    mut v_as_1847_: *mut LeanObject,
    mut v_as_x27_1848_: *mut LeanObject,
    mut v_b_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___redArg(
            v_as_x27_1848_,
            v_b_1849_,
        );
    return v___x_1851_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1___boxed(
    mut v_as_1852_: *mut LeanObject,
    mut v_as_x27_1853_: *mut LeanObject,
    mut v_b_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_getFunNamesToMatch_spec__1(
            v_as_1852_,
            v_as_x27_1853_,
            v_b_1854_,
            v_a_1855_,
        );
    lean_dec(v_as_x27_1853_);
    lean_dec(v_as_1852_);
    return v_res_1856_;
}
pub unsafe fn l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(
    mut v_x_1857_: *mut LeanObject,
) -> u8 {
    let mut v___x_1858_: u8 = 0;
    let mut v_head_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: u8 = 0;
    let mut v_tail_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1857_) == 0 {
                    v___x_1858_ = 0;
                    return v___x_1858_;
                } else {
                    v_head_1859_ = lean_ctor_get(v_x_1857_, 0);
                    v_pvars_1860_ = lean_ctor_get(v_head_1859_, 2);
                    if lean_obj_tag(v_pvars_1860_) == 1 {
                        v_head_1861_ = lean_ctor_get(v_pvars_1860_, 0);
                        if lean_obj_tag(v_head_1861_) == 1 {
                            v___x_1862_ = 1;
                            return v___x_1862_;
                        } else {
                            v_tail_1863_ = lean_ctor_get(v_x_1857_, 1);
                            v_x_1857_ = v_tail_1863_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_1865_ = lean_ctor_get(v_x_1857_, 1);
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
    mut v_x_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1868_: u8 = 0;
    let mut v_r_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_x_1867_);
    lean_dec(v_x_1867_);
    v_r_1869_ = lean_box((v_res_1868_) as usize);
    return v_r_1869_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_shouldSaveActual(mut v_alts_1870_: *mut LeanObject) -> u8 {
    let mut v___x_1871_: u8 = 0;
    v___x_1871_ =
        l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(v_alts_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_shouldSaveActual___boxed(
    mut v_alts_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1873_: u8 = 0;
    let mut v_r_1874_: *mut LeanObject = core::ptr::null_mut();
    v_res_1873_ = l_Lean_Elab_Term_MatchExpr_shouldSaveActual(v_alts_1872_);
    lean_dec(v_alts_1872_);
    v_r_1874_ = lean_box((v_res_1873_) as usize);
    return v_r_1874_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
    mut v_funName_1875_: *mut LeanObject,
    mut v_x_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u8 = 0;
    let mut v___x_1889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1876_) == 0 {
                    v___x_1877_ = lean_box(0);
                    return v___x_1877_;
                } else {
                    v_head_1878_ = lean_ctor_get(v_x_1876_, 0);
                    v_tail_1879_ = lean_ctor_get(v_x_1876_, 1);
                    v_funName_1884_ = lean_ctor_get(v_head_1878_, 1);
                    v_pvars_1885_ = lean_ctor_get(v_head_1878_, 2);
                    v___x_1886_ = l_Lean_TSyntax_getId(v_funName_1884_);
                    v___x_1887_ = l_Lean_TSyntax_getId(v_funName_1875_);
                    v___x_1888_ = lean_name_eq(v___x_1886_, v___x_1887_);
                    lean_dec(v___x_1887_);
                    lean_dec(v___x_1886_);
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
                    lean_inc(v_head_1878_);
                    v___x_1883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1883_, 0, v_head_1878_);
                    return v___x_1883_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0___boxed(
    mut v_funName_1890_: *mut LeanObject,
    mut v_x_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1892_: *mut LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
        v_funName_1890_,
        v_x_1891_,
    );
    lean_dec(v_x_1891_);
    lean_dec(v_funName_1890_);
    return v_res_1892_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(
    mut v_alts_1893_: *mut LeanObject,
    mut v_funName_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    v___x_1895_ = l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
        v_funName_1894_,
        v_alts_1893_,
    );
    return v___x_1895_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getAltFor_x3f___boxed(
    mut v_alts_1896_: *mut LeanObject,
    mut v_funName_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1898_: *mut LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_Elab_Term_MatchExpr_getAltFor_x3f(v_alts_1896_, v_funName_1897_);
    lean_dec(v_funName_1897_);
    lean_dec(v_alts_1896_);
    return v_res_1898_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(
    mut v_actual_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v_head_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_unused_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1900_) == 0 {
                    lean_dec(v_actual_1899_);
                    v___x_1902_ = lean_array_to_list(v_a_1901_);
                    return v___x_1902_;
                } else {
                    v_head_1903_ = lean_ctor_get(v_a_1900_, 0);
                    lean_inc(v_head_1903_);
                    v_tail_1904_ = lean_ctor_get(v_a_1900_, 1);
                    lean_inc(v_tail_1904_);
                    lean_dec_ref_known(v_a_1900_, 2);
                    v_var_x3f_1909_ = lean_ctor_get(v_head_1903_, 0);
                    v_funName_1910_ = lean_ctor_get(v_head_1903_, 1);
                    v_pvars_1911_ = lean_ctor_get(v_head_1903_, 2);
                    v_rhs_1912_ = lean_ctor_get(v_head_1903_, 3);
                    v_k_1913_ = lean_ctor_get(v_head_1903_, 4);
                    v_actuals_1914_ = lean_ctor_get(v_head_1903_, 5);
                    v_isSharedCheck_1937_ = (!lean_is_exclusive(v_head_1903_)) as u8;
                    if v_isSharedCheck_1937_ == 0 {
                        v___x_1916_ = v_head_1903_;
                        v_isShared_1917_ = v_isSharedCheck_1937_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_actuals_1914_);
                        lean_inc(v_k_1913_);
                        lean_inc(v_rhs_1912_);
                        lean_inc(v_pvars_1911_);
                        lean_inc(v_funName_1910_);
                        lean_inc(v_var_x3f_1909_);
                        lean_dec(v_head_1903_);
                        v___x_1916_ = lean_box(0);
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
                if lean_obj_tag(v_pvars_1911_) == 1 {
                    v_head_1926_ = lean_ctor_get(v_pvars_1911_, 0);
                    if lean_obj_tag(v_head_1926_) == 1 {
                        lean_del_object(v___x_1916_);
                        v_tail_1927_ = lean_ctor_get(v_pvars_1911_, 1);
                        v_isSharedCheck_1935_ = (!lean_is_exclusive(v_pvars_1911_)) as u8;
                        if v_isSharedCheck_1935_ == 0 {
                            v_unused_1936_ = lean_ctor_get(v_pvars_1911_, 0);
                            lean_dec(v_unused_1936_);
                            v___x_1929_ = v_pvars_1911_;
                            v_isShared_1930_ = v_isSharedCheck_1935_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_tail_1927_);
                            lean_dec(v_pvars_1911_);
                            v___x_1929_ = lean_box(0);
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
                if lean_obj_tag(v_pvars_1911_) == 1 {
                    v_head_1919_ = lean_ctor_get(v_pvars_1911_, 0);
                    if lean_obj_tag(v_head_1919_) == 0 {
                        v_tail_1920_ = lean_ctor_get(v_pvars_1911_, 1);
                        lean_inc(v_tail_1920_);
                        lean_dec_ref_known(v_pvars_1911_, 2);
                        if v_isShared_1917_ == 0 {
                            lean_ctor_set(v___x_1916_, 2, v_tail_1920_);
                            v___x_1922_ = v___x_1916_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 6, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_var_x3f_1909_);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_funName_1910_);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_tail_1920_);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_rhs_1912_);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_k_1913_);
                            lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_actuals_1914_);
                            v___x_1922_ = v_reuseFailAlloc_1923_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_pvars_1911_, 2);
                        lean_del_object(v___x_1916_);
                        lean_dec(v_actuals_1914_);
                        lean_dec(v_k_1913_);
                        lean_dec(v_rhs_1912_);
                        lean_dec(v_funName_1910_);
                        lean_dec(v_var_x3f_1909_);
                        v_a_1900_ = v_tail_1904_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1916_);
                    lean_dec(v_actuals_1914_);
                    lean_dec(v_k_1913_);
                    lean_dec(v_rhs_1912_);
                    lean_dec(v_pvars_1911_);
                    lean_dec(v_funName_1910_);
                    lean_dec(v_var_x3f_1909_);
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
                lean_inc(v_actual_1899_);
                if v_isShared_1930_ == 0 {
                    lean_ctor_set(v___x_1929_, 1, v_actuals_1914_);
                    lean_ctor_set(v___x_1929_, 0, v_actual_1899_);
                    v___x_1932_ = v___x_1929_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_actual_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_actuals_1914_);
                    v___x_1932_ = v_reuseFailAlloc_1934_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1933_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_1933_, 0, v_var_x3f_1909_);
                lean_ctor_set(v___x_1933_, 1, v_funName_1910_);
                lean_ctor_set(v___x_1933_, 2, v_tail_1927_);
                lean_ctor_set(v___x_1933_, 3, v_rhs_1912_);
                lean_ctor_set(v___x_1933_, 4, v_k_1913_);
                lean_ctor_set(v___x_1933_, 5, v___x_1932_);
                v_val_1906_ = v___x_1933_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_next(
    mut v_alts_1940_: *mut LeanObject,
    mut v_actual_1941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_Elab_Term_MatchExpr_next___closed__0;
    v___x_1943_ = l_List_filterMapTR_go___at___00Lean_Elab_Term_MatchExpr_next_spec__0(
        v_actual_1941_,
        v_alts_1940_,
        v___x_1942_,
    );
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1() -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_Elab_Term_MatchExpr_initK___closed__0;
    v___x_1946_ = l_String_toRawSubstring_x27(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_initK(
    mut v_alt_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1957_: u8 = 0;
    let mut v_quotContext_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_x3f_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funName_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_1952_ = lean_ctor_get(v_a_1951_, 0);
                v_traceMsgs_1953_ = lean_ctor_get(v_a_1951_, 1);
                v_expandedMacroDecls_1954_ = lean_ctor_get(v_a_1951_, 2);
                v_isSharedCheck_1986_ = (!lean_is_exclusive(v_a_1951_)) as u8;
                if v_isSharedCheck_1986_ == 0 {
                    v___x_1956_ = v_a_1951_;
                    v_isShared_1957_ = v_isSharedCheck_1986_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_1954_);
                    lean_inc(v_traceMsgs_1953_);
                    lean_inc(v_macroScope_1952_);
                    lean_dec(v_a_1951_);
                    v___x_1956_ = lean_box(0);
                    v_isShared_1957_ = v_isSharedCheck_1986_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_1958_ = lean_ctor_get(v_a_1950_, 1);
                v_ref_1959_ = lean_ctor_get(v_a_1950_, 5);
                v_var_x3f_1960_ = lean_ctor_get(v_alt_1949_, 0);
                v_funName_1961_ = lean_ctor_get(v_alt_1949_, 1);
                v_pvars_1962_ = lean_ctor_get(v_alt_1949_, 2);
                v_rhs_1963_ = lean_ctor_get(v_alt_1949_, 3);
                v_actuals_1964_ = lean_ctor_get(v_alt_1949_, 5);
                v_isSharedCheck_1984_ = (!lean_is_exclusive(v_alt_1949_)) as u8;
                if v_isSharedCheck_1984_ == 0 {
                    v_unused_1985_ = lean_ctor_get(v_alt_1949_, 4);
                    lean_dec(v_unused_1985_);
                    v___x_1966_ = v_alt_1949_;
                    v_isShared_1967_ = v_isSharedCheck_1984_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_actuals_1964_);
                    lean_inc(v_rhs_1963_);
                    lean_inc(v_pvars_1962_);
                    lean_inc(v_funName_1961_);
                    lean_inc(v_var_x3f_1960_);
                    lean_dec(v_alt_1949_);
                    v___x_1966_ = lean_box(0);
                    v_isShared_1967_ = v_isSharedCheck_1984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1968_ = lean_unsigned_to_nat(1);
                v___x_1969_ = lean_nat_add(v_macroScope_1952_, v___x_1968_);
                v___x_1970_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1_once),
                    _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1,
                );
                if v_isShared_1957_ == 0 {
                    lean_ctor_set(v___x_1956_, 0, v___x_1969_);
                    v___x_1972_ = v___x_1956_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1969_);
                    lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_traceMsgs_1953_);
                    lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_expandedMacroDecls_1954_);
                    v___x_1972_ = v_reuseFailAlloc_1983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1973_ = 0;
                v___x_1974_ = l_Lean_SourceInfo_fromRef(v_ref_1959_, v___x_1973_);
                v___x_1975_ = l_Lean_Elab_Term_MatchExpr_initK___closed__2;
                lean_inc(v_quotContext_1958_);
                v___x_1976_ =
                    l_Lean_addMacroScope(v_quotContext_1958_, v___x_1975_, v_macroScope_1952_);
                v___x_1977_ = lean_box(0);
                v___x_1978_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1978_, 0, v___x_1974_);
                lean_ctor_set(v___x_1978_, 1, v___x_1970_);
                lean_ctor_set(v___x_1978_, 2, v___x_1976_);
                lean_ctor_set(v___x_1978_, 3, v___x_1977_);
                if v_isShared_1967_ == 0 {
                    lean_ctor_set(v___x_1966_, 4, v___x_1978_);
                    v___x_1980_ = v___x_1966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_var_x3f_1960_);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_funName_1961_);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_pvars_1962_);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_rhs_1963_);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 4, v___x_1978_);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 5, v_actuals_1964_);
                    v___x_1980_ = v_reuseFailAlloc_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1981_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1981_, 0, v___x_1980_);
                lean_ctor_set(v___x_1981_, 1, v___x_1972_);
                return v___x_1981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_initK___boxed(
    mut v_alt_1987_: *mut LeanObject,
    mut v_a_1988_: *mut LeanObject,
    mut v_a_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1990_: *mut LeanObject = core::ptr::null_mut();
    v_res_1990_ = l_Lean_Elab_Term_MatchExpr_initK(v_alt_1987_, v_a_1988_, v_a_1989_);
    lean_dec_ref(v_a_1988_);
    return v_res_1990_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(
    mut v_sz_1991_: usize,
    mut v_i_1992_: usize,
    mut v_bs_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1994_: u8 = 0;
    let mut v_v_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: usize = 0;
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1994_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
                if v___x_1994_ == 0 {
                    return v_bs_1993_;
                } else {
                    v_v_1995_ = lean_array_uget(v_bs_1993_, v_i_1992_);
                    v___x_1996_ = lean_unsigned_to_nat(0);
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
    mut v_sz_2002_: *mut LeanObject,
    mut v_i_2003_: *mut LeanObject,
    mut v_bs_2004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2005_: usize = 0;
    let mut v_i_boxed_2006_: usize = 0;
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2002_);
    lean_dec(v_sz_2002_);
    v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
    lean_dec(v_i_2003_);
    v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_boxed_2005_, v_i_boxed_2006_, v_bs_2004_);
    return v_res_2007_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__6;
    v___x_2021_ = l_String_toRawSubstring_x27(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14()
-> *mut LeanObject {
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    v___x_2038_ = l_Array_mkArray0(lean_box(0));
    return v___x_2038_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(
    mut v_as_2040_: *mut LeanObject,
    mut v_i_2041_: usize,
    mut v_stop_2042_: usize,
    mut v_b_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: usize = 0;
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_usize_dec_eq(v_i_2041_, v_stop_2042_);
                if v___x_2052_ == 0 {
                    v___x_2053_ = lean_array_uget_borrowed(v_as_2040_, v_i_2041_);
                    if lean_obj_tag(v___x_2053_) == 0 {
                        v_a_2047_ = v_b_2043_;
                        v_a_2048_ = v___y_2045_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2054_ = lean_ctor_get(v___x_2053_, 0);
                        v_quotContext_2055_ = lean_ctor_get(v___y_2044_, 1);
                        v_currMacroScope_2056_ = lean_ctor_get(v___y_2044_, 2);
                        v_ref_2057_ = lean_ctor_get(v___y_2044_, 5);
                        v___x_2058_ = l_Lean_SourceInfo_fromRef(v_ref_2057_, v___x_2052_);
                        v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                        v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                        lean_inc_n(v___x_2058_, 7);
                        v___x_2061_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2061_, 0, v___x_2058_);
                        lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                        v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                        lean_inc(v_val_2054_);
                        v___x_2063_ = l_Lean_Syntax_node1(v___x_2058_, v___x_2062_, v_val_2054_);
                        v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                        v___x_2065_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2065_, 0, v___x_2058_);
                        lean_ctor_set(v___x_2065_, 1, v___x_2064_);
                        v___x_2066_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
                        v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8;
                        lean_inc(v_currMacroScope_2056_);
                        lean_inc(v_quotContext_2055_);
                        v___x_2068_ = l_Lean_addMacroScope(
                            v_quotContext_2055_,
                            v___x_2067_,
                            v_currMacroScope_2056_,
                        );
                        v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13;
                        v___x_2070_ = lean_alloc_ctor(3, 4, (0) as u32);
                        lean_ctor_set(v___x_2070_, 0, v___x_2058_);
                        lean_ctor_set(v___x_2070_, 1, v___x_2066_);
                        lean_ctor_set(v___x_2070_, 2, v___x_2068_);
                        lean_ctor_set(v___x_2070_, 3, v___x_2069_);
                        v___x_2071_ =
                            l_Lean_Syntax_node2(v___x_2058_, v___x_2062_, v___x_2065_, v___x_2070_);
                        v___x_2072_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                        v___x_2073_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_2073_, 0, v___x_2058_);
                        lean_ctor_set(v___x_2073_, 1, v___x_2062_);
                        lean_ctor_set(v___x_2073_, 2, v___x_2072_);
                        v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                        v___x_2075_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2075_, 0, v___x_2058_);
                        lean_ctor_set(v___x_2075_, 1, v___x_2074_);
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
                    v___x_2078_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2078_, 0, v_b_2043_);
                    lean_ctor_set(v___x_2078_, 1, v___y_2045_);
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
    mut v_as_2079_: *mut LeanObject,
    mut v_i_2080_: *mut LeanObject,
    mut v_stop_2081_: *mut LeanObject,
    mut v_b_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2085_: usize = 0;
    let mut v_stop_boxed_2086_: usize = 0;
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2085_ = lean_unbox_usize(v_i_2080_);
    lean_dec(v_i_2080_);
    v_stop_boxed_2086_ = lean_unbox_usize(v_stop_2081_);
    lean_dec(v_stop_2081_);
    v_res_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2079_, v_i_boxed_2085_, v_stop_boxed_2086_, v_b_2082_, v___y_2083_, v___y_2084_);
    lean_dec_ref(v___y_2083_);
    lean_dec_ref(v_as_2079_);
    return v_res_2087_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
    mut v_as_2088_: *mut LeanObject,
    mut v_start_2089_: *mut LeanObject,
    mut v_stop_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    v___x_2093_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
    v___x_2094_ = lean_nat_dec_lt(v_start_2089_, v_stop_2090_);
    if v___x_2094_ == 0 {
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        v___x_2095_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2095_, 0, v___x_2093_);
        lean_ctor_set(v___x_2095_, 1, v___y_2092_);
        return v___x_2095_;
    } else {
        let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: u8 = 0;
        v___x_2096_ = lean_array_get_size(v_as_2088_);
        v___x_2097_ = lean_nat_dec_le(v_stop_2090_, v___x_2096_);
        if v___x_2097_ == 0 {
            let mut v___x_2098_: u8 = 0;
            v___x_2098_ = lean_nat_dec_lt(v_start_2089_, v___x_2096_);
            if v___x_2098_ == 0 {
                let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
                v___x_2099_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2099_, 0, v___x_2093_);
                lean_ctor_set(v___x_2099_, 1, v___y_2092_);
                return v___x_2099_;
            } else {
                let mut v___x_2100_: usize = 0;
                let mut v___x_2101_: usize = 0;
                let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
                v___x_2100_ = lean_usize_of_nat(v_start_2089_);
                v___x_2101_ = lean_usize_of_nat(v___x_2096_);
                v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2088_, v___x_2100_, v___x_2101_, v___x_2093_, v___y_2091_, v___y_2092_);
                return v___x_2102_;
            }
        } else {
            let mut v___x_2103_: usize = 0;
            let mut v___x_2104_: usize = 0;
            let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
            v___x_2103_ = lean_usize_of_nat(v_start_2089_);
            v___x_2104_ = lean_usize_of_nat(v_stop_2090_);
            v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0(v_as_2088_, v___x_2103_, v___x_2104_, v___x_2093_, v___y_2091_, v___y_2092_);
            return v___x_2105_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0___boxed(
    mut v_as_2106_: *mut LeanObject,
    mut v_start_2107_: *mut LeanObject,
    mut v_stop_2108_: *mut LeanObject,
    mut v___y_2109_: *mut LeanObject,
    mut v___y_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
        v_as_2106_,
        v_start_2107_,
        v_stop_2108_,
        v___y_2109_,
        v___y_2110_,
    );
    lean_dec_ref(v___y_2109_);
    lean_dec(v_stop_2108_);
    lean_dec(v_start_2107_);
    lean_dec_ref(v_as_2106_);
    return v_res_2111_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2() -> *mut LeanObject {
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    v___x_2114_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__1;
    v___x_2115_ = l_String_toRawSubstring_x27(v___x_2114_);
    return v___x_2115_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getParams(
    mut v_alt_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_var_x3f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pvars_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v_sz_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_params_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_var_x3f_2132_ = lean_ctor_get(v_alt_2129_, 0);
                lean_inc(v_var_x3f_2132_);
                v_pvars_2133_ = lean_ctor_get(v_alt_2129_, 2);
                lean_inc(v_pvars_2133_);
                lean_dec_ref(v_alt_2129_);
                v_params_2191_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
                if lean_obj_tag(v_var_x3f_2132_) == 1 {
                    v_val_2192_ = lean_ctor_get(v_var_x3f_2132_, 0);
                    lean_inc(v_val_2192_);
                    lean_dec_ref_known(v_var_x3f_2132_, 1);
                    v_quotContext_2193_ = lean_ctor_get(v_a_2130_, 1);
                    v_currMacroScope_2194_ = lean_ctor_get(v_a_2130_, 2);
                    v_ref_2195_ = lean_ctor_get(v_a_2130_, 5);
                    v___x_2196_ = 0;
                    v___x_2197_ = l_Lean_SourceInfo_fromRef(v_ref_2195_, v___x_2196_);
                    v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                    v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    lean_inc_n(v___x_2197_, 7);
                    v___x_2200_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2200_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                    v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2202_ = l_Lean_Syntax_node1(v___x_2197_, v___x_2201_, v_val_2192_);
                    v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                    v___x_2204_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2204_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2204_, 1, v___x_2203_);
                    v___x_2205_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__7);
                    v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__8;
                    lean_inc(v_currMacroScope_2194_);
                    lean_inc(v_quotContext_2193_);
                    v___x_2207_ = l_Lean_addMacroScope(
                        v_quotContext_2193_,
                        v___x_2206_,
                        v_currMacroScope_2194_,
                    );
                    v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__13;
                    v___x_2209_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2209_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2209_, 1, v___x_2205_);
                    lean_ctor_set(v___x_2209_, 2, v___x_2207_);
                    lean_ctor_set(v___x_2209_, 3, v___x_2208_);
                    v___x_2210_ =
                        l_Lean_Syntax_node2(v___x_2197_, v___x_2201_, v___x_2204_, v___x_2209_);
                    v___x_2211_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2212_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2212_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2212_, 1, v___x_2201_);
                    lean_ctor_set(v___x_2212_, 2, v___x_2211_);
                    v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2214_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2214_, 0, v___x_2197_);
                    lean_ctor_set(v___x_2214_, 1, v___x_2213_);
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
                    lean_dec(v_var_x3f_2132_);
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
                v___x_2140_ = lean_unsigned_to_nat(0);
                v___x_2141_ = lean_array_get_size(v___x_2139_);
                v___x_2142_ =
                    l_Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0(
                        v___x_2139_,
                        v___x_2140_,
                        v___x_2141_,
                        v___y_2136_,
                        v___y_2137_,
                    );
                lean_dec_ref(v___x_2139_);
                if lean_obj_tag(v___x_2142_) == 0 {
                    v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
                    v_a_2144_ = lean_ctor_get(v___x_2142_, 1);
                    v_isSharedCheck_2190_ = (!lean_is_exclusive(v___x_2142_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2146_ = v___x_2142_;
                        v_isShared_2147_ = v_isSharedCheck_2190_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2144_);
                        lean_inc(v_a_2143_);
                        lean_dec(v___x_2142_);
                        v___x_2146_ = lean_box(0);
                        v_isShared_2147_ = v_isSharedCheck_2190_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_params_2135_);
                    return v___x_2142_;
                }
            }
            2 => {
                v___x_2148_ = l_Array_append___redArg(v_params_2135_, v_a_2143_);
                lean_dec(v_a_2143_);
                v___x_2149_ = lean_array_get_size(v___x_2148_);
                v___x_2150_ = lean_nat_dec_eq(v___x_2149_, v___x_2140_);
                if v___x_2150_ == 0 {
                    v_sz_2151_ = lean_array_size(v___x_2148_);
                    v___x_2152_ = 0usize;
                    v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_MatchExpr_getParams_spec__1(v_sz_2151_, v___x_2152_, v___x_2148_);
                    if v_isShared_2147_ == 0 {
                        lean_ctor_set(v___x_2146_, 0, v___x_2153_);
                        v___x_2155_ = v___x_2146_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
                        lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_a_2144_);
                        v___x_2155_ = v_reuseFailAlloc_2156_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2148_);
                    v_quotContext_2157_ = lean_ctor_get(v___y_2136_, 1);
                    v_currMacroScope_2158_ = lean_ctor_get(v___y_2136_, 2);
                    v_ref_2159_ = lean_ctor_get(v___y_2136_, 5);
                    v___x_2160_ = 0;
                    v___x_2161_ = l_Lean_SourceInfo_fromRef(v_ref_2159_, v___x_2160_);
                    v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                    v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    lean_inc_n(v___x_2161_, 9);
                    v___x_2164_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2164_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2164_, 1, v___x_2163_);
                    v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2166_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                    v___x_2167_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                    v___x_2168_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2168_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2168_, 1, v___x_2167_);
                    v___x_2169_ = l_Lean_Syntax_node1(v___x_2161_, v___x_2166_, v___x_2168_);
                    v___x_2170_ = l_Lean_Syntax_node1(v___x_2161_, v___x_2165_, v___x_2169_);
                    v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                    v___x_2172_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2172_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2172_, 1, v___x_2171_);
                    v___x_2173_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2,
                    );
                    v___x_2174_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__3;
                    lean_inc(v_currMacroScope_2158_);
                    lean_inc(v_quotContext_2157_);
                    v___x_2175_ = l_Lean_addMacroScope(
                        v_quotContext_2157_,
                        v___x_2174_,
                        v_currMacroScope_2158_,
                    );
                    v___x_2176_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__7;
                    v___x_2177_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2177_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2177_, 1, v___x_2173_);
                    lean_ctor_set(v___x_2177_, 2, v___x_2175_);
                    lean_ctor_set(v___x_2177_, 3, v___x_2176_);
                    v___x_2178_ =
                        l_Lean_Syntax_node2(v___x_2161_, v___x_2165_, v___x_2172_, v___x_2177_);
                    v___x_2179_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2180_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2180_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2180_, 1, v___x_2165_);
                    lean_ctor_set(v___x_2180_, 2, v___x_2179_);
                    v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2182_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2182_, 0, v___x_2161_);
                    lean_ctor_set(v___x_2182_, 1, v___x_2181_);
                    v___x_2183_ = l_Lean_Syntax_node5(
                        v___x_2161_,
                        v___x_2162_,
                        v___x_2164_,
                        v___x_2170_,
                        v___x_2178_,
                        v___x_2180_,
                        v___x_2182_,
                    );
                    v___x_2184_ = lean_unsigned_to_nat(1);
                    v___x_2185_ = lean_mk_empty_array_with_capacity(v___x_2184_);
                    v___x_2186_ = lean_array_push(v___x_2185_, v___x_2183_);
                    if v_isShared_2147_ == 0 {
                        lean_ctor_set(v___x_2146_, 0, v___x_2186_);
                        v___x_2188_ = v___x_2146_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
                        lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_a_2144_);
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
    mut v_alt_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2220_: *mut LeanObject = core::ptr::null_mut();
    v_res_2220_ = l_Lean_Elab_Term_MatchExpr_getParams(v_alt_2217_, v_a_2218_, v_a_2219_);
    lean_dec_ref(v_a_2218_);
    return v_res_2220_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7() -> *mut LeanObject {
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__6;
    v___x_2238_ = l_String_toRawSubstring_x27(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getActuals(
    mut v_discr_2277_: *mut LeanObject,
    mut v_alt_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_var_x3f_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actuals_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_var_x3f_2281_ = lean_ctor_get(v_alt_2278_, 0);
                lean_inc(v_var_x3f_2281_);
                v_actuals_2282_ = lean_ctor_get(v_alt_2278_, 5);
                lean_inc(v_actuals_2282_);
                lean_dec_ref(v_alt_2278_);
                v_actuals_2320_ = l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch___closed__0;
                if lean_obj_tag(v_var_x3f_2281_) == 0 {
                    lean_dec(v_discr_2277_);
                    v_actuals_2284_ = v_actuals_2320_;
                    v___y_2285_ = v_a_2279_;
                    v___y_2286_ = v_a_2280_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_var_x3f_2281_, 1);
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
                lean_dec_ref(v___x_2287_);
                v___x_2289_ = lean_array_get_size(v_actuals_2288_);
                v___x_2290_ = lean_unsigned_to_nat(0);
                v___x_2291_ = lean_nat_dec_eq(v___x_2289_, v___x_2290_);
                if v___x_2291_ == 0 {
                    v___x_2292_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2292_, 0, v_actuals_2288_);
                    lean_ctor_set(v___x_2292_, 1, v___y_2286_);
                    return v___x_2292_;
                } else {
                    lean_dec_ref(v_actuals_2288_);
                    v_quotContext_2293_ = lean_ctor_get(v___y_2285_, 1);
                    v_currMacroScope_2294_ = lean_ctor_get(v___y_2285_, 2);
                    v_ref_2295_ = lean_ctor_get(v___y_2285_, 5);
                    v___x_2296_ = 0;
                    v___x_2297_ = l_Lean_SourceInfo_fromRef(v_ref_2295_, v___x_2296_);
                    v___x_2298_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                    v___x_2299_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                    v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    lean_inc_n(v___x_2297_, 6);
                    v___x_2301_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2301_, 0, v___x_2297_);
                    lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                    v___x_2302_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                    v___x_2303_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                    );
                    v___x_2304_ = lean_box(0);
                    lean_inc(v_currMacroScope_2294_);
                    lean_inc(v_quotContext_2293_);
                    v___x_2305_ = l_Lean_addMacroScope(
                        v_quotContext_2293_,
                        v___x_2304_,
                        v_currMacroScope_2294_,
                    );
                    v___x_2306_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                    v___x_2307_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2307_, 0, v___x_2297_);
                    lean_ctor_set(v___x_2307_, 1, v___x_2303_);
                    lean_ctor_set(v___x_2307_, 2, v___x_2305_);
                    lean_ctor_set(v___x_2307_, 3, v___x_2306_);
                    v___x_2308_ = l_Lean_Syntax_node1(v___x_2297_, v___x_2302_, v___x_2307_);
                    v___x_2309_ =
                        l_Lean_Syntax_node2(v___x_2297_, v___x_2299_, v___x_2301_, v___x_2308_);
                    v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2312_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2312_, 0, v___x_2297_);
                    lean_ctor_set(v___x_2312_, 1, v___x_2310_);
                    lean_ctor_set(v___x_2312_, 2, v___x_2311_);
                    v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2314_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2314_, 0, v___x_2297_);
                    lean_ctor_set(v___x_2314_, 1, v___x_2313_);
                    v___x_2315_ = l_Lean_Syntax_node3(
                        v___x_2297_,
                        v___x_2298_,
                        v___x_2309_,
                        v___x_2312_,
                        v___x_2314_,
                    );
                    v___x_2316_ = lean_unsigned_to_nat(1);
                    v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
                    v___x_2318_ = lean_array_push(v___x_2317_, v___x_2315_);
                    v___x_2319_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2319_, 0, v___x_2318_);
                    lean_ctor_set(v___x_2319_, 1, v___y_2286_);
                    return v___x_2319_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_getActuals___boxed(
    mut v_discr_2322_: *mut LeanObject,
    mut v_alt_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
    mut v_a_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2326_: *mut LeanObject = core::ptr::null_mut();
    v_res_2326_ =
        l_Lean_Elab_Term_MatchExpr_getActuals(v_discr_2322_, v_alt_2323_, v_a_2324_, v_a_2325_);
    lean_dec_ref(v_a_2324_);
    return v_res_2326_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3() -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__2;
    v___x_2335_ = l_Lean_mkAtom(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4() -> *mut LeanObject {
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    v___x_2336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3,
    );
    v___x_2337_ = lean_unsigned_to_nat(3);
    v___x_2338_ = lean_mk_empty_array_with_capacity(v___x_2337_);
    v___x_2339_ = lean_array_push(v___x_2338_, v___x_2336_);
    return v___x_2339_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5() -> *mut LeanObject {
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    v___x_2340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__3,
    );
    v___x_2341_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__4,
    );
    v___x_2342_ = lean_array_push(v___x_2341_, v___x_2340_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(
    mut v_ident_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__1;
    v___x_2345_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5_once),
        _init_l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName___closed__5,
    );
    v___x_2346_ = lean_array_push(v___x_2345_, v_ident_2343_);
    v___x_2347_ = lean_box(2);
    v___x_2348_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2348_, 0, v___x_2347_);
    lean_ctor_set(v___x_2348_, 1, v___x_2344_);
    lean_ctor_set(v___x_2348_, 2, v___x_2346_);
    return v___x_2348_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(
    mut v___x_2349_: u8,
    mut v_____do__lift_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2350_, v___x_2349_);
    v___x_2354_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    lean_ctor_set(v___x_2354_, 1, v___y_2352_);
    return v___x_2354_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0___boxed(
    mut v___x_2355_: *mut LeanObject,
    mut v_____do__lift_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_20980__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_20980__boxed_2359_ = (lean_unbox(v___x_2355_) as u8);
    v_res_2360_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(
            v___x_20980__boxed_2359_,
            v_____do__lift_2356_,
            v___y_2357_,
            v___y_2358_,
        );
    lean_dec_ref(v___y_2357_);
    lean_dec(v_____do__lift_2356_);
    return v_res_2360_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v___x_2382_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__8;
    v___x_2383_ = l_String_toRawSubstring_x27(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(
    mut v_alts_2391_: *mut LeanObject,
    mut v_discr_2392_: *mut LeanObject,
    mut v_as_x27_2393_: *mut LeanObject,
    mut v_b_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v_quotContext_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2393_) == 0 {
                    lean_dec(v_discr_2392_);
                    v___x_2397_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2397_, 0, v_b_2394_);
                    lean_ctor_set(v___x_2397_, 1, v___y_2396_);
                    return v___x_2397_;
                } else {
                    v_head_2398_ = lean_ctor_get(v_as_x27_2393_, 0);
                    v_tail_2399_ = lean_ctor_get(v_as_x27_2393_, 1);
                    v___x_2400_ =
                        l_List_find_x3f___at___00Lean_Elab_Term_MatchExpr_getAltFor_x3f_spec__0(
                            v_head_2398_,
                            v_alts_2391_,
                        );
                    if lean_obj_tag(v___x_2400_) == 1 {
                        v_val_2401_ = lean_ctor_get(v___x_2400_, 0);
                        lean_inc_n(v_val_2401_, 2);
                        lean_dec_ref_known(v___x_2400_, 1);
                        lean_inc(v_discr_2392_);
                        v___x_2402_ = l_Lean_Elab_Term_MatchExpr_getActuals(
                            v_discr_2392_,
                            v_val_2401_,
                            v___y_2395_,
                            v___y_2396_,
                        );
                        v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
                        v_a_2404_ = lean_ctor_get(v___x_2402_, 1);
                        v_isSharedCheck_2458_ = (!lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2458_ == 0 {
                            v___x_2406_ = v___x_2402_;
                            v_isShared_2407_ = v_isSharedCheck_2458_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2404_);
                            lean_inc(v_a_2403_);
                            lean_dec(v___x_2402_);
                            v___x_2406_ = lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2400_);
                        v_as_x27_2393_ = v_tail_2399_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_2408_ = lean_ctor_get(v___y_2395_, 1);
                v_currMacroScope_2409_ = lean_ctor_get(v___y_2395_, 2);
                v_ref_2410_ = lean_ctor_get(v___y_2395_, 5);
                v___x_2411_ = 0;
                v___x_2412_ = l_Lean_SourceInfo_fromRef(v_ref_2410_, v___x_2411_);
                v___x_2413_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                lean_inc(v___x_2412_);
                if v_isShared_2407_ == 0 {
                    lean_ctor_set_tag(v___x_2406_, 2);
                    lean_ctor_set(v___x_2406_, 1, v___x_2413_);
                    lean_ctor_set(v___x_2406_, 0, v___x_2412_);
                    v___x_2415_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2412_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2413_);
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
                lean_inc_n(v___x_2412_, 15);
                v___x_2421_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2421_, 0, v___x_2412_);
                lean_ctor_set(v___x_2421_, 1, v___x_2420_);
                v___x_2422_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2423_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2424_ = lean_box(0);
                lean_inc_n(v_currMacroScope_2409_, 2);
                lean_inc_n(v_quotContext_2408_, 2);
                v___x_2425_ =
                    l_Lean_addMacroScope(v_quotContext_2408_, v___x_2424_, v_currMacroScope_2409_);
                v___x_2426_ = lean_box(0);
                v___x_2427_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2428_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2428_, 0, v___x_2412_);
                lean_ctor_set(v___x_2428_, 1, v___x_2423_);
                lean_ctor_set(v___x_2428_, 2, v___x_2425_);
                lean_ctor_set(v___x_2428_, 3, v___x_2427_);
                v___x_2429_ = l_Lean_Syntax_node1(v___x_2412_, v___x_2422_, v___x_2428_);
                v___x_2430_ =
                    l_Lean_Syntax_node2(v___x_2412_, v___x_2419_, v___x_2421_, v___x_2429_);
                v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2432_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2432_, 0, v___x_2412_);
                lean_ctor_set(v___x_2432_, 1, v___x_2431_);
                lean_inc(v_discr_2392_);
                v___x_2433_ = l_Lean_Syntax_node3(
                    v___x_2412_,
                    v___x_2418_,
                    v___x_2430_,
                    v_discr_2392_,
                    v___x_2432_,
                );
                v___x_2434_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2435_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2435_, 0, v___x_2412_);
                lean_ctor_set(v___x_2435_, 1, v___x_2434_);
                v___x_2436_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__9);
                v___x_2437_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__10;
                v___x_2438_ =
                    l_Lean_addMacroScope(v_quotContext_2408_, v___x_2437_, v_currMacroScope_2409_);
                v___x_2439_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2439_, 0, v___x_2412_);
                lean_ctor_set(v___x_2439_, 1, v___x_2436_);
                lean_ctor_set(v___x_2439_, 2, v___x_2438_);
                lean_ctor_set(v___x_2439_, 3, v___x_2426_);
                v___x_2440_ = l_Lean_Syntax_node3(
                    v___x_2412_,
                    v___x_2417_,
                    v___x_2433_,
                    v___x_2435_,
                    v___x_2439_,
                );
                v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                lean_inc(v_head_2398_);
                v___x_2442_ = l_Lean_Elab_Term_MatchExpr_toDoubleQuotedName(v_head_2398_);
                v___x_2443_ = l_Lean_Syntax_node1(v___x_2412_, v___x_2441_, v___x_2442_);
                v_k_2444_ = lean_ctor_get(v_val_2401_, 4);
                lean_inc(v_k_2444_);
                lean_dec(v_val_2401_);
                v___x_2445_ =
                    l_Lean_Syntax_node2(v___x_2412_, v___x_2416_, v___x_2440_, v___x_2443_);
                v___x_2446_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__12;
                v___x_2447_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2448_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2448_, 0, v___x_2412_);
                lean_ctor_set(v___x_2448_, 1, v___x_2447_);
                v___x_2449_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2450_ = l_Array_append___redArg(v___x_2449_, v_a_2403_);
                lean_dec(v_a_2403_);
                v___x_2451_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2412_);
                lean_ctor_set(v___x_2451_, 1, v___x_2441_);
                lean_ctor_set(v___x_2451_, 2, v___x_2450_);
                v___x_2452_ = l_Lean_Syntax_node2(v___x_2412_, v___x_2416_, v_k_2444_, v___x_2451_);
                v___x_2453_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__14;
                v___x_2454_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2454_, 0, v___x_2412_);
                lean_ctor_set(v___x_2454_, 1, v___x_2453_);
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
    mut v_alts_2460_: *mut LeanObject,
    mut v_discr_2461_: *mut LeanObject,
    mut v_as_x27_2462_: *mut LeanObject,
    mut v_b_2463_: *mut LeanObject,
    mut v___y_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2460_, v_discr_2461_, v_as_x27_2462_, v_b_2463_, v___y_2464_, v___y_2465_);
    lean_dec_ref(v___y_2464_);
    lean_dec(v_as_x27_2462_);
    lean_dec(v_alts_2460_);
    return v_res_2466_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1()
-> *mut LeanObject {
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2468_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__0;
    v___x_2469_ = l_String_toRawSubstring_x27(v___x_2468_);
    return v___x_2469_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8()
-> *mut LeanObject {
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v___x_2480_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__7;
    v___x_2481_ = l_String_toRawSubstring_x27(v___x_2480_);
    return v___x_2481_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11()
-> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2485_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__10;
    v___x_2486_ = l_String_toRawSubstring_x27(v___x_2485_);
    return v___x_2486_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25()
-> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__24;
    v___x_2522_ = l_String_toRawSubstring_x27(v___x_2521_);
    return v___x_2522_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33()
-> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__32;
    v___x_2540_ = l_String_toRawSubstring_x27(v___x_2539_);
    return v___x_2540_;
}
pub unsafe fn _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36()
-> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2544_ =
        l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__35;
    v___x_2545_ = l_String_toRawSubstring_x27(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
    mut v_kElse_2560_: *mut LeanObject,
    mut v_discr_2561_: *mut LeanObject,
    mut v_alts_2562_: *mut LeanObject,
    mut v_a_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v_methods_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funNamesToMatch_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveActual_2577_: u8 = 0;
    let mut v_actual_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_altsNext_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v_quotContext_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_a_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v_quotContext_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_2565_ = lean_ctor_get(v_a_2564_, 0);
                v_traceMsgs_2566_ = lean_ctor_get(v_a_2564_, 1);
                v_expandedMacroDecls_2567_ = lean_ctor_get(v_a_2564_, 2);
                v_isSharedCheck_2837_ = (!lean_is_exclusive(v_a_2564_)) as u8;
                if v_isSharedCheck_2837_ == 0 {
                    v___x_2569_ = v_a_2564_;
                    v_isShared_2570_ = v_isSharedCheck_2837_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_2567_);
                    lean_inc(v_traceMsgs_2566_);
                    lean_inc(v_macroScope_2565_);
                    lean_dec(v_a_2564_);
                    v___x_2569_ = lean_box(0);
                    v_isShared_2570_ = v_isSharedCheck_2837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_methods_2571_ = lean_ctor_get(v_a_2563_, 0);
                v_quotContext_2572_ = lean_ctor_get(v_a_2563_, 1);
                v_currRecDepth_2573_ = lean_ctor_get(v_a_2563_, 3);
                v_maxRecDepth_2574_ = lean_ctor_get(v_a_2563_, 4);
                v_ref_2575_ = lean_ctor_get(v_a_2563_, 5);
                v_funNamesToMatch_2576_ =
                    l_Lean_Elab_Term_MatchExpr_getFunNamesToMatch(v_alts_2562_);
                v_saveActual_2577_ =
                    l_List_any___at___00Lean_Elab_Term_MatchExpr_shouldSaveActual_spec__0(
                        v_alts_2562_,
                    );
                v___x_2819_ = lean_unsigned_to_nat(1);
                v___x_2820_ = lean_nat_add(v_macroScope_2565_, v___x_2819_);
                if v_isShared_2570_ == 0 {
                    lean_ctor_set(v___x_2569_, 0, v___x_2820_);
                    v___x_2822_ = v___x_2569_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2820_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_traceMsgs_2566_);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_expandedMacroDecls_2567_);
                    v___x_2822_ = v_reuseFailAlloc_2836_;
                    state = 11;
                    continue;
                }
            }
            2 => {
                lean_inc(v_alts_2562_);
                v_altsNext_2582_ = l_Lean_Elab_Term_MatchExpr_next(v_alts_2562_, v_actual_2579_);
                v___x_2583_ = l_List_isEmpty___redArg(v_altsNext_2582_);
                if v___x_2583_ == 0 {
                    v_quotContext_2584_ = lean_ctor_get(v___y_2580_, 1);
                    v_currMacroScope_2585_ = lean_ctor_get(v___y_2580_, 2);
                    v_ref_2586_ = lean_ctor_get(v___y_2580_, 5);
                    v___x_2587_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_2583_, v_ref_2586_, v___y_2580_, v___y_2581_);
                    if lean_obj_tag(v___x_2587_) == 0 {
                        v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
                        lean_inc(v_a_2588_);
                        v_a_2589_ = lean_ctor_get(v___x_2587_, 1);
                        lean_inc(v_a_2589_);
                        lean_dec_ref_known(v___x_2587_, 2);
                        v___x_2590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
                        v___x_2591_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2;
                        lean_inc(v_currMacroScope_2585_);
                        lean_inc(v_quotContext_2584_);
                        v___x_2592_ = l_Lean_addMacroScope(
                            v_quotContext_2584_,
                            v___x_2591_,
                            v_currMacroScope_2585_,
                        );
                        v___x_2593_ = lean_box(0);
                        lean_inc(v___x_2592_);
                        v___x_2594_ = lean_alloc_ctor(3, 4, (0) as u32);
                        lean_ctor_set(v___x_2594_, 0, v_a_2588_);
                        lean_ctor_set(v___x_2594_, 1, v___x_2590_);
                        lean_ctor_set(v___x_2594_, 2, v___x_2592_);
                        lean_ctor_set(v___x_2594_, 3, v___x_2593_);
                        lean_inc(v_kElse_2560_);
                        v___x_2595_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(v_kElse_2560_, v___x_2594_, v_altsNext_2582_, v___y_2580_, v_a_2589_);
                        if lean_obj_tag(v___x_2595_) == 0 {
                            if v_saveActual_2577_ == 0 {
                                v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
                                v_a_2597_ = lean_ctor_get(v___x_2595_, 1);
                                v_isSharedCheck_2676_ = (!lean_is_exclusive(v___x_2595_)) as u8;
                                if v_isSharedCheck_2676_ == 0 {
                                    v___x_2599_ = v___x_2595_;
                                    v_isShared_2600_ = v_isSharedCheck_2676_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2597_);
                                    lean_inc(v_a_2596_);
                                    lean_dec(v___x_2595_);
                                    v___x_2599_ = lean_box(0);
                                    v_isShared_2600_ = v_isSharedCheck_2676_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_2677_ = lean_ctor_get(v___x_2595_, 0);
                                v_a_2678_ = lean_ctor_get(v___x_2595_, 1);
                                v_isSharedCheck_2782_ = (!lean_is_exclusive(v___x_2595_)) as u8;
                                if v_isSharedCheck_2782_ == 0 {
                                    v___x_2680_ = v___x_2595_;
                                    v_isShared_2681_ = v_isSharedCheck_2782_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2678_);
                                    lean_inc(v_a_2677_);
                                    lean_dec(v___x_2595_);
                                    v___x_2680_ = lean_box(0);
                                    v_isShared_2681_ = v_isSharedCheck_2782_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2592_);
                            lean_dec_ref(v___y_2580_);
                            lean_dec(v_funNamesToMatch_2576_);
                            lean_dec(v_alts_2562_);
                            lean_dec(v_discr_2561_);
                            lean_dec(v_kElse_2560_);
                            return v___x_2595_;
                        }
                    } else {
                        lean_dec(v_altsNext_2582_);
                        lean_dec_ref(v___y_2580_);
                        lean_dec(v_funNamesToMatch_2576_);
                        lean_dec(v_alts_2562_);
                        lean_dec(v_discr_2561_);
                        lean_dec(v_kElse_2560_);
                        v_a_2783_ = lean_ctor_get(v___x_2587_, 0);
                        v_a_2784_ = lean_ctor_get(v___x_2587_, 1);
                        v_isSharedCheck_2791_ = (!lean_is_exclusive(v___x_2587_)) as u8;
                        if v_isSharedCheck_2791_ == 0 {
                            v___x_2786_ = v___x_2587_;
                            v_isShared_2787_ = v_isSharedCheck_2791_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2784_);
                            lean_inc(v_a_2783_);
                            lean_dec(v___x_2587_);
                            v___x_2786_ = lean_box(0);
                            v_isShared_2787_ = v_isSharedCheck_2791_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_altsNext_2582_);
                    v_quotContext_2792_ = lean_ctor_get(v___y_2580_, 1);
                    v_currMacroScope_2793_ = lean_ctor_get(v___y_2580_, 2);
                    v_ref_2794_ = lean_ctor_get(v___y_2580_, 5);
                    v___x_2795_ = 0;
                    v___x_2796_ = l_Lean_SourceInfo_fromRef(v_ref_2794_, v___x_2795_);
                    v___x_2797_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                    v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                    v___x_2799_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__1;
                    v___x_2800_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                    v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                    lean_inc_n(v___x_2796_, 8);
                    v___x_2802_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2802_, 0, v___x_2796_);
                    lean_ctor_set(v___x_2802_, 1, v___x_2801_);
                    v___x_2803_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                    v___x_2804_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once
                        ),
                        _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                    );
                    v___x_2805_ = lean_box(0);
                    lean_inc(v_currMacroScope_2793_);
                    lean_inc(v_quotContext_2792_);
                    v___x_2806_ = l_Lean_addMacroScope(
                        v_quotContext_2792_,
                        v___x_2805_,
                        v_currMacroScope_2793_,
                    );
                    v___x_2807_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                    v___x_2808_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2808_, 0, v___x_2796_);
                    lean_ctor_set(v___x_2808_, 1, v___x_2804_);
                    lean_ctor_set(v___x_2808_, 2, v___x_2806_);
                    lean_ctor_set(v___x_2808_, 3, v___x_2807_);
                    v___x_2809_ = l_Lean_Syntax_node1(v___x_2796_, v___x_2803_, v___x_2808_);
                    v___x_2810_ =
                        l_Lean_Syntax_node2(v___x_2796_, v___x_2800_, v___x_2802_, v___x_2809_);
                    v___x_2811_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                    v___x_2812_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2812_, 0, v___x_2796_);
                    lean_ctor_set(v___x_2812_, 1, v___x_2798_);
                    lean_ctor_set(v___x_2812_, 2, v___x_2811_);
                    v___x_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                    v___x_2814_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2814_, 0, v___x_2796_);
                    lean_ctor_set(v___x_2814_, 1, v___x_2813_);
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
                    lean_dec_ref(v___y_2580_);
                    lean_dec(v_funNamesToMatch_2576_);
                    lean_dec(v_alts_2562_);
                    return v___x_2818_;
                }
            }
            3 => {
                v___x_2601_ = l_Lean_SourceInfo_fromRef(v_ref_2586_, v_saveActual_2577_);
                v___x_2602_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4;
                v___x_2603_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                lean_inc(v___x_2601_);
                if v_isShared_2600_ == 0 {
                    lean_ctor_set_tag(v___x_2599_, 2);
                    lean_ctor_set(v___x_2599_, 1, v___x_2603_);
                    lean_ctor_set(v___x_2599_, 0, v___x_2601_);
                    v___x_2605_ = v___x_2599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2601_);
                    lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2603_);
                    v___x_2605_ = v_reuseFailAlloc_2675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2606_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6;
                v___x_2607_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
                v___x_2608_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9;
                lean_inc_n(v_currMacroScope_2585_, 4);
                lean_inc_n(v_quotContext_2584_, 4);
                v___x_2609_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2608_, v_currMacroScope_2585_);
                lean_inc_n(v___x_2601_, 30);
                v___x_2610_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v___x_2601_);
                lean_ctor_set(v___x_2610_, 1, v___x_2607_);
                lean_ctor_set(v___x_2610_, 2, v___x_2609_);
                lean_ctor_set(v___x_2610_, 3, v___x_2593_);
                lean_inc_ref(v___x_2610_);
                v___x_2611_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2606_, v___x_2610_);
                v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_2613_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2613_, 0, v___x_2601_);
                lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                v___x_2614_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4;
                v___x_2615_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6;
                v___x_2616_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                v___x_2618_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2618_, 0, v___x_2601_);
                lean_ctor_set(v___x_2618_, 1, v___x_2617_);
                v___x_2619_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2620_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2621_ = lean_box(0);
                v___x_2622_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2621_, v_currMacroScope_2585_);
                v___x_2623_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2624_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2624_, 0, v___x_2601_);
                lean_ctor_set(v___x_2624_, 1, v___x_2620_);
                lean_ctor_set(v___x_2624_, 2, v___x_2622_);
                lean_ctor_set(v___x_2624_, 3, v___x_2623_);
                v___x_2625_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2619_, v___x_2624_);
                v___x_2626_ =
                    l_Lean_Syntax_node2(v___x_2601_, v___x_2616_, v___x_2618_, v___x_2625_);
                v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2628_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2628_, 0, v___x_2601_);
                lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                lean_inc_ref(v___x_2628_);
                lean_inc_n(v_discr_2561_, 2);
                lean_inc(v___x_2626_);
                v___x_2629_ = l_Lean_Syntax_node3(
                    v___x_2601_,
                    v___x_2615_,
                    v___x_2626_,
                    v_discr_2561_,
                    v___x_2628_,
                );
                v___x_2630_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2631_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2631_, 0, v___x_2601_);
                lean_ctor_set(v___x_2631_, 1, v___x_2630_);
                v___x_2632_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
                v___x_2633_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12;
                v___x_2634_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2633_, v_currMacroScope_2585_);
                v___x_2635_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2635_, 0, v___x_2601_);
                lean_ctor_set(v___x_2635_, 1, v___x_2632_);
                lean_ctor_set(v___x_2635_, 2, v___x_2634_);
                lean_ctor_set(v___x_2635_, 3, v___x_2593_);
                v___x_2636_ = l_Lean_Syntax_node3(
                    v___x_2601_,
                    v___x_2614_,
                    v___x_2629_,
                    v___x_2631_,
                    v___x_2635_,
                );
                v___x_2637_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2638_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2638_, 0, v___x_2601_);
                lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                v___x_2639_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_2640_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_2641_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2641_, 0, v___x_2601_);
                lean_ctor_set(v___x_2641_, 1, v___x_2639_);
                v___x_2642_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_2644_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2645_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2645_, 0, v___x_2601_);
                lean_ctor_set(v___x_2645_, 1, v___x_2643_);
                lean_ctor_set(v___x_2645_, 2, v___x_2644_);
                lean_inc_ref_n(v___x_2645_, 3);
                v___x_2646_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2642_, v___x_2645_);
                v___x_2647_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_2648_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_2649_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                v___x_2650_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2650_, 0, v___x_2601_);
                lean_ctor_set(v___x_2650_, 1, v___x_2590_);
                lean_ctor_set(v___x_2650_, 2, v___x_2592_);
                lean_ctor_set(v___x_2650_, 3, v___x_2593_);
                v___x_2651_ = l_Lean_Syntax_node1(v___x_2601_, v___x_2649_, v___x_2650_);
                v___x_2652_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                v___x_2653_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2653_, 0, v___x_2601_);
                lean_ctor_set(v___x_2653_, 1, v___x_2652_);
                v___x_2654_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_2655_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
                v___x_2656_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27;
                v___x_2657_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2656_, v_currMacroScope_2585_);
                v___x_2658_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30;
                v___x_2659_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2659_, 0, v___x_2601_);
                lean_ctor_set(v___x_2659_, 1, v___x_2655_);
                lean_ctor_set(v___x_2659_, 2, v___x_2657_);
                lean_ctor_set(v___x_2659_, 3, v___x_2658_);
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
                v___x_2665_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2665_, 0, v___x_2601_);
                lean_ctor_set(v___x_2665_, 1, v___x_2664_);
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
                v___x_2668_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2668_, 0, v___x_2601_);
                lean_ctor_set(v___x_2668_, 1, v___x_2667_);
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
                lean_dec_ref(v___y_2580_);
                lean_dec(v_funNamesToMatch_2576_);
                lean_dec(v_alts_2562_);
                return v___x_2674_;
            }
            5 => {
                v___x_2682_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___lam__0(v___x_2583_, v_ref_2586_, v___y_2580_, v_a_2678_);
                if lean_obj_tag(v___x_2682_) == 0 {
                    v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
                    lean_inc_n(v_a_2683_, 2);
                    v_a_2684_ = lean_ctor_get(v___x_2682_, 1);
                    lean_inc(v_a_2684_);
                    lean_dec_ref_known(v___x_2682_, 2);
                    v___x_2685_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__4;
                    v___x_2686_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__0;
                    if v_isShared_2681_ == 0 {
                        lean_ctor_set_tag(v___x_2680_, 2);
                        lean_ctor_set(v___x_2680_, 1, v___x_2686_);
                        lean_ctor_set(v___x_2680_, 0, v_a_2683_);
                        v___x_2688_ = v___x_2680_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2772_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2683_);
                        lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2686_);
                        v___x_2688_ = v_reuseFailAlloc_2772_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2680_);
                    lean_dec(v_a_2677_);
                    lean_dec(v___x_2592_);
                    lean_dec_ref(v___y_2580_);
                    lean_dec(v_funNamesToMatch_2576_);
                    lean_dec(v_alts_2562_);
                    lean_dec(v_discr_2561_);
                    lean_dec(v_kElse_2560_);
                    v_a_2773_ = lean_ctor_get(v___x_2682_, 0);
                    v_a_2774_ = lean_ctor_get(v___x_2682_, 1);
                    v_isSharedCheck_2781_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                    if v_isSharedCheck_2781_ == 0 {
                        v___x_2776_ = v___x_2682_;
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2774_);
                        lean_inc(v_a_2773_);
                        lean_dec(v___x_2682_);
                        v___x_2776_ = lean_box(0);
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2689_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__6;
                v___x_2690_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__8);
                v___x_2691_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__9;
                lean_inc_n(v_currMacroScope_2585_, 6);
                lean_inc_n(v_quotContext_2584_, 6);
                v___x_2692_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2691_, v_currMacroScope_2585_);
                lean_inc_n(v_a_2683_, 37);
                v___x_2693_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2693_, 0, v_a_2683_);
                lean_ctor_set(v___x_2693_, 1, v___x_2690_);
                lean_ctor_set(v___x_2693_, 2, v___x_2692_);
                lean_ctor_set(v___x_2693_, 3, v___x_2593_);
                lean_inc_ref(v___x_2693_);
                v___x_2694_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2689_, v___x_2693_);
                v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_2696_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2696_, 0, v_a_2683_);
                lean_ctor_set(v___x_2696_, 1, v___x_2695_);
                v___x_2697_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__4;
                v___x_2698_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__6;
                v___x_2699_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__3;
                v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                v___x_2701_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2701_, 0, v_a_2683_);
                lean_ctor_set(v___x_2701_, 1, v___x_2700_);
                v___x_2702_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__5;
                v___x_2703_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getActuals___closed__7_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getActuals___closed__7,
                );
                v___x_2704_ = lean_box(0);
                v___x_2705_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2704_, v_currMacroScope_2585_);
                v___x_2706_ = l_Lean_Elab_Term_MatchExpr_getActuals___closed__21;
                v___x_2707_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2707_, 0, v_a_2683_);
                lean_ctor_set(v___x_2707_, 1, v___x_2703_);
                lean_ctor_set(v___x_2707_, 2, v___x_2705_);
                lean_ctor_set(v___x_2707_, 3, v___x_2706_);
                v___x_2708_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2702_, v___x_2707_);
                v___x_2709_ = l_Lean_Syntax_node2(v_a_2683_, v___x_2699_, v___x_2701_, v___x_2708_);
                v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_2711_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2711_, 0, v_a_2683_);
                lean_ctor_set(v___x_2711_, 1, v___x_2710_);
                lean_inc_ref(v___x_2711_);
                lean_inc_n(v_discr_2561_, 2);
                lean_inc(v___x_2709_);
                v___x_2712_ = l_Lean_Syntax_node3(
                    v_a_2683_,
                    v___x_2698_,
                    v___x_2709_,
                    v_discr_2561_,
                    v___x_2711_,
                );
                v___x_2713_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__7;
                v___x_2714_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2714_, 0, v_a_2683_);
                lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__11);
                v___x_2716_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__12;
                v___x_2717_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2716_, v_currMacroScope_2585_);
                v___x_2718_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2718_, 0, v_a_2683_);
                lean_ctor_set(v___x_2718_, 1, v___x_2715_);
                lean_ctor_set(v___x_2718_, 2, v___x_2717_);
                lean_ctor_set(v___x_2718_, 3, v___x_2593_);
                v___x_2719_ = l_Lean_Syntax_node3(
                    v_a_2683_,
                    v___x_2697_,
                    v___x_2712_,
                    v___x_2714_,
                    v___x_2718_,
                );
                v___x_2720_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__13;
                v___x_2721_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2721_, 0, v_a_2683_);
                lean_ctor_set(v___x_2721_, 1, v___x_2720_);
                v___x_2722_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_2723_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_2724_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2724_, 0, v_a_2683_);
                lean_ctor_set(v___x_2724_, 1, v___x_2722_);
                v___x_2725_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_2727_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_2728_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2728_, 0, v_a_2683_);
                lean_ctor_set(v___x_2728_, 1, v___x_2726_);
                lean_ctor_set(v___x_2728_, 2, v___x_2727_);
                lean_inc_ref_n(v___x_2728_, 5);
                v___x_2729_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2725_, v___x_2728_);
                v___x_2730_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_2731_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_2732_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                v___x_2733_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
                v___x_2734_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34;
                v___x_2735_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2734_, v_currMacroScope_2585_);
                v___x_2736_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2736_, 0, v_a_2683_);
                lean_ctor_set(v___x_2736_, 1, v___x_2733_);
                lean_ctor_set(v___x_2736_, 2, v___x_2735_);
                lean_ctor_set(v___x_2736_, 3, v___x_2593_);
                v___x_2737_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2732_, v___x_2736_);
                v___x_2738_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                v___x_2739_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2739_, 0, v_a_2683_);
                lean_ctor_set(v___x_2739_, 1, v___x_2738_);
                v___x_2740_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_2741_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__36);
                v___x_2742_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__38;
                v___x_2743_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2742_, v_currMacroScope_2585_);
                v___x_2744_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__41;
                v___x_2745_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2745_, 0, v_a_2683_);
                lean_ctor_set(v___x_2745_, 1, v___x_2741_);
                lean_ctor_set(v___x_2745_, 2, v___x_2743_);
                lean_ctor_set(v___x_2745_, 3, v___x_2744_);
                v___x_2746_ =
                    l_Lean_Syntax_node2(v_a_2683_, v___x_2726_, v_discr_2561_, v___x_2693_);
                lean_inc(v___x_2746_);
                v___x_2747_ = l_Lean_Syntax_node2(v_a_2683_, v___x_2740_, v___x_2745_, v___x_2746_);
                lean_inc_ref(v___x_2739_);
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
                v___x_2751_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2751_, 0, v_a_2683_);
                lean_ctor_set(v___x_2751_, 1, v___x_2750_);
                v___x_2752_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2752_, 0, v_a_2683_);
                lean_ctor_set(v___x_2752_, 1, v___x_2590_);
                lean_ctor_set(v___x_2752_, 2, v___x_2592_);
                lean_ctor_set(v___x_2752_, 3, v___x_2593_);
                v___x_2753_ = l_Lean_Syntax_node1(v_a_2683_, v___x_2732_, v___x_2752_);
                v___x_2754_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__25);
                v___x_2755_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__27;
                v___x_2756_ =
                    l_Lean_addMacroScope(v_quotContext_2584_, v___x_2755_, v_currMacroScope_2585_);
                v___x_2757_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__30;
                v___x_2758_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2758_, 0, v_a_2683_);
                lean_ctor_set(v___x_2758_, 1, v___x_2754_);
                lean_ctor_set(v___x_2758_, 2, v___x_2756_);
                lean_ctor_set(v___x_2758_, 3, v___x_2757_);
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
                lean_inc_ref(v___x_2751_);
                lean_inc(v___x_2729_);
                lean_inc_ref(v___x_2724_);
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
                v___x_2765_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2765_, 0, v_a_2683_);
                lean_ctor_set(v___x_2765_, 1, v___x_2764_);
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
                lean_dec_ref(v___y_2580_);
                lean_dec(v_funNamesToMatch_2576_);
                lean_dec(v_alts_2562_);
                return v___x_2771_;
            }
            7 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2773_);
                    lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_a_2774_);
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
                    v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2789_;
            }
            11 => {
                lean_inc(v_ref_2575_);
                lean_inc(v_maxRecDepth_2574_);
                lean_inc(v_currRecDepth_2573_);
                lean_inc(v_macroScope_2565_);
                lean_inc(v_quotContext_2572_);
                lean_inc(v_methods_2571_);
                v___x_2823_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2823_, 0, v_methods_2571_);
                lean_ctor_set(v___x_2823_, 1, v_quotContext_2572_);
                lean_ctor_set(v___x_2823_, 2, v_macroScope_2565_);
                lean_ctor_set(v___x_2823_, 3, v_currRecDepth_2573_);
                lean_ctor_set(v___x_2823_, 4, v_maxRecDepth_2574_);
                lean_ctor_set(v___x_2823_, 5, v_ref_2575_);
                if v_saveActual_2577_ == 0 {
                    lean_dec(v_macroScope_2565_);
                    v___x_2824_ = l_Lean_SourceInfo_fromRef(v_ref_2575_, v_saveActual_2577_);
                    v___x_2825_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                    v___x_2826_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                    lean_inc(v___x_2824_);
                    v___x_2827_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2827_, 0, v___x_2824_);
                    lean_ctor_set(v___x_2827_, 1, v___x_2826_);
                    v___x_2828_ = l_Lean_Syntax_node1(v___x_2824_, v___x_2825_, v___x_2827_);
                    v_actual_2579_ = v___x_2828_;
                    v___y_2580_ = v___x_2823_;
                    v___y_2581_ = v___x_2822_;
                    state = 2;
                    continue;
                } else {
                    v___x_2829_ = 0;
                    v___x_2830_ = l_Lean_SourceInfo_fromRef(v_ref_2575_, v___x_2829_);
                    v___x_2831_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__33);
                    v___x_2832_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__34;
                    lean_inc(v_quotContext_2572_);
                    v___x_2833_ =
                        l_Lean_addMacroScope(v_quotContext_2572_, v___x_2832_, v_macroScope_2565_);
                    v___x_2834_ = lean_box(0);
                    v___x_2835_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2835_, 0, v___x_2830_);
                    lean_ctor_set(v___x_2835_, 1, v___x_2831_);
                    lean_ctor_set(v___x_2835_, 2, v___x_2833_);
                    lean_ctor_set(v___x_2835_, 3, v___x_2834_);
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
    mut v_kElse_2838_: *mut LeanObject,
    mut v_discr_2839_: *mut LeanObject,
    mut v_alts_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2843_: *mut LeanObject = core::ptr::null_mut();
    v_res_2843_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
        v_kElse_2838_,
        v_discr_2839_,
        v_alts_2840_,
        v_a_2841_,
        v_a_2842_,
    );
    lean_dec_ref(v_a_2841_);
    return v_res_2843_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(
    mut v_alts_2844_: *mut LeanObject,
    mut v_discr_2845_: *mut LeanObject,
    mut v_as_2846_: *mut LeanObject,
    mut v_as_x27_2847_: *mut LeanObject,
    mut v_b_2848_: *mut LeanObject,
    mut v_a_2849_: *mut LeanObject,
    mut v___y_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    v___x_2852_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg(v_alts_2844_, v_discr_2845_, v_as_x27_2847_, v_b_2848_, v___y_2850_, v___y_2851_);
    return v___x_2852_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___boxed(
    mut v_alts_2853_: *mut LeanObject,
    mut v_discr_2854_: *mut LeanObject,
    mut v_as_2855_: *mut LeanObject,
    mut v_as_x27_2856_: *mut LeanObject,
    mut v_b_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2861_: *mut LeanObject = core::ptr::null_mut();
    v_res_2861_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0(v_alts_2853_, v_discr_2854_, v_as_2855_, v_as_x27_2856_, v_b_2857_, v_a_2858_, v___y_2859_, v___y_2860_);
    lean_dec_ref(v___y_2859_);
    lean_dec(v_as_x27_2856_);
    lean_dec(v_as_2855_);
    lean_dec(v_alts_2853_);
    return v_res_2861_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate___lam__0(
    mut v_____do__lift_2862_: *mut LeanObject,
    mut v___y_2863_: *mut LeanObject,
    mut v___y_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    v___x_2865_ = 0;
    v___x_2866_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2862_, v___x_2865_);
    v___x_2867_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2867_, 0, v___x_2866_);
    lean_ctor_set(v___x_2867_, 1, v___y_2864_);
    return v___x_2867_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate___lam__0___boxed(
    mut v_____do__lift_2868_: *mut LeanObject,
    mut v___y_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
        v_____do__lift_2868_,
        v___y_2869_,
        v___y_2870_,
    );
    lean_dec_ref(v___y_2869_);
    lean_dec(v_____do__lift_2868_);
    return v_res_2871_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
    mut v_as_x27_2878_: *mut LeanObject,
    mut v_b_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2878_) == 0 {
                    v___x_2882_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2882_, 0, v_b_2879_);
                    lean_ctor_set(v___x_2882_, 1, v___y_2881_);
                    return v___x_2882_;
                } else {
                    v_head_2883_ = lean_ctor_get(v_as_x27_2878_, 0);
                    v_tail_2884_ = lean_ctor_get(v_as_x27_2878_, 1);
                    lean_inc(v_head_2883_);
                    v___x_2885_ = l_Lean_Elab_Term_MatchExpr_getParams(
                        v_head_2883_,
                        v___y_2880_,
                        v___y_2881_,
                    );
                    if lean_obj_tag(v___x_2885_) == 0 {
                        v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
                        lean_inc(v_a_2886_);
                        v_a_2887_ = lean_ctor_get(v___x_2885_, 1);
                        lean_inc(v_a_2887_);
                        lean_dec_ref_known(v___x_2885_, 2);
                        v_ref_2888_ = lean_ctor_get(v___y_2880_, 5);
                        v___x_2889_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0;
                        v___x_2890_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1;
                        v___x_2891_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                        v_rhs_2892_ = lean_ctor_get(v_head_2883_, 3);
                        v_k_2893_ = lean_ctor_get(v_head_2883_, 4);
                        v___x_2894_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                        v___x_2895_ = 0;
                        v___x_2896_ = l_Lean_SourceInfo_fromRef(v_ref_2888_, v___x_2895_);
                        lean_inc_n(v___x_2896_, 8);
                        v___x_2897_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2897_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2897_, 1, v___x_2889_);
                        v___x_2898_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                        lean_inc(v_k_2893_);
                        v___x_2899_ = l_Lean_Syntax_node1(v___x_2896_, v___x_2898_, v_k_2893_);
                        v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                        v___x_2901_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                        v___x_2902_ = l_Array_append___redArg(v___x_2901_, v_a_2886_);
                        lean_dec(v_a_2886_);
                        v___x_2903_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_2903_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2903_, 1, v___x_2900_);
                        lean_ctor_set(v___x_2903_, 2, v___x_2902_);
                        v___x_2904_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_2904_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2904_, 1, v___x_2900_);
                        lean_ctor_set(v___x_2904_, 2, v___x_2901_);
                        v___x_2905_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__23;
                        v___x_2906_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2906_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2906_, 1, v___x_2905_);
                        lean_inc(v_rhs_2892_);
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
                        v___x_2910_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_2910_, 0, v___x_2896_);
                        lean_ctor_set(v___x_2910_, 1, v___x_2909_);
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
                        lean_dec(v_b_2879_);
                        v_a_2913_ = lean_ctor_get(v___x_2885_, 0);
                        v_a_2914_ = lean_ctor_get(v___x_2885_, 1);
                        v_isSharedCheck_2921_ = (!lean_is_exclusive(v___x_2885_)) as u8;
                        if v_isSharedCheck_2921_ == 0 {
                            v___x_2916_ = v___x_2885_;
                            v_isShared_2917_ = v_isSharedCheck_2921_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2914_);
                            lean_inc(v_a_2913_);
                            lean_dec(v___x_2885_);
                            v___x_2916_ = lean_box(0);
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
                    v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_a_2914_);
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
    mut v_as_x27_2922_: *mut LeanObject,
    mut v_b_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2926_: *mut LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
        v_as_x27_2922_,
        v_b_2923_,
        v___y_2924_,
        v___y_2925_,
    );
    lean_dec_ref(v___y_2924_);
    lean_dec(v_as_x27_2922_);
    return v_res_2926_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
    mut v_x_2927_: *mut LeanObject,
    mut v_x_2928_: *mut LeanObject,
    mut v___y_2929_: *mut LeanObject,
    mut v___y_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2927_) == 0 {
                    v___x_2931_ = l_List_reverse___redArg(v_x_2928_);
                    v___x_2932_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2932_, 0, v___x_2931_);
                    lean_ctor_set(v___x_2932_, 1, v___y_2930_);
                    return v___x_2932_;
                } else {
                    v_head_2933_ = lean_ctor_get(v_x_2927_, 0);
                    v_tail_2934_ = lean_ctor_get(v_x_2927_, 1);
                    v_isSharedCheck_2945_ = (!lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2945_ == 0 {
                        v___x_2936_ = v_x_2927_;
                        v_isShared_2937_ = v_isSharedCheck_2945_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2934_);
                        lean_inc(v_head_2933_);
                        lean_dec(v_x_2927_);
                        v___x_2936_ = lean_box(0);
                        v_isShared_2937_ = v_isSharedCheck_2945_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2938_ =
                    l_Lean_Elab_Term_MatchExpr_initK(v_head_2933_, v___y_2929_, v___y_2930_);
                v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
                lean_inc(v_a_2939_);
                v_a_2940_ = lean_ctor_get(v___x_2938_, 1);
                lean_inc(v_a_2940_);
                lean_dec_ref(v___x_2938_);
                if v_isShared_2937_ == 0 {
                    lean_ctor_set(v___x_2936_, 1, v_x_2928_);
                    lean_ctor_set(v___x_2936_, 0, v_a_2939_);
                    v___x_2942_ = v___x_2936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2939_);
                    lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_x_2928_);
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
    mut v_x_2946_: *mut LeanObject,
    mut v_x_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
        v_x_2946_,
        v_x_2947_,
        v___y_2948_,
        v___y_2949_,
    );
    lean_dec_ref(v___y_2948_);
    return v_res_2950_;
}
pub unsafe fn _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4() -> *mut LeanObject {
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_Elab_Term_MatchExpr_generate___closed__3;
    v___x_2962_ = l_String_toRawSubstring_x27(v___x_2961_);
    return v___x_2962_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_generate(
    mut v_discr_2977_: *mut LeanObject,
    mut v_alts_2978_: *mut LeanObject,
    mut v_elseAlt_2979_: *mut LeanObject,
    mut v_a_2980_: *mut LeanObject,
    mut v_a_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_a_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3091_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3095_: u8 = 0;
    let mut v_reuseFailAlloc_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_a_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3104_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3108_: u8 = 0;
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_a_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2982_ = lean_box(0);
                v___x_2983_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__0(
                    v_alts_2978_,
                    v___x_2982_,
                    v_a_2980_,
                    v_a_2981_,
                );
                if lean_obj_tag(v___x_2983_) == 0 {
                    v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
                    lean_inc(v_a_2984_);
                    v_a_2985_ = lean_ctor_get(v___x_2983_, 1);
                    lean_inc(v_a_2985_);
                    lean_dec_ref_known(v___x_2983_, 2);
                    v_quotContext_2986_ = lean_ctor_get(v_a_2980_, 1);
                    v_currMacroScope_2987_ = lean_ctor_get(v_a_2980_, 2);
                    v_ref_2988_ = lean_ctor_get(v_a_2980_, 5);
                    v___x_2989_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
                        v_ref_2988_,
                        v_a_2980_,
                        v_a_2985_,
                    );
                    v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
                    v_a_2991_ = lean_ctor_get(v___x_2989_, 1);
                    v_isSharedCheck_3110_ = (!lean_is_exclusive(v___x_2989_)) as u8;
                    if v_isSharedCheck_3110_ == 0 {
                        v___x_2993_ = v___x_2989_;
                        v_isShared_2994_ = v_isSharedCheck_3110_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2991_);
                        lean_inc(v_a_2990_);
                        lean_dec(v___x_2989_);
                        v___x_2993_ = lean_box(0);
                        v_isShared_2994_ = v_isSharedCheck_3110_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_elseAlt_2979_);
                    lean_dec(v_discr_2977_);
                    v_a_3111_ = lean_ctor_get(v___x_2983_, 0);
                    v_a_3112_ = lean_ctor_get(v___x_2983_, 1);
                    v_isSharedCheck_3119_ = (!lean_is_exclusive(v___x_2983_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3114_ = v___x_2983_;
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3112_);
                        lean_inc(v_a_3111_);
                        lean_dec(v___x_2983_);
                        v___x_3114_ = lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2995_ =
                    l_Lean_Elab_Term_MatchExpr_generate___lam__0(v_ref_2988_, v_a_2980_, v_a_2991_);
                v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
                v_a_2997_ = lean_ctor_get(v___x_2995_, 1);
                v_isSharedCheck_3109_ = (!lean_is_exclusive(v___x_2995_)) as u8;
                if v_isSharedCheck_3109_ == 0 {
                    v___x_2999_ = v___x_2995_;
                    v_isShared_3000_ = v_isSharedCheck_3109_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2997_);
                    lean_inc(v_a_2996_);
                    lean_dec(v___x_2995_);
                    v___x_2999_ = lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3001_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1_once), _init_l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__1);
                v___x_3002_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__2;
                lean_inc_n(v_currMacroScope_2987_, 2);
                lean_inc_n(v_quotContext_2986_, 2);
                v___x_3003_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3002_, v_currMacroScope_2987_);
                lean_inc(v___x_3003_);
                v___x_3004_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3004_, 0, v_a_2990_);
                lean_ctor_set(v___x_3004_, 1, v___x_3001_);
                lean_ctor_set(v___x_3004_, 2, v___x_3003_);
                lean_ctor_set(v___x_3004_, 3, v___x_2982_);
                v___x_3005_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_initK___closed__1_once),
                    _init_l_Lean_Elab_Term_MatchExpr_initK___closed__1,
                );
                v___x_3006_ = l_Lean_Elab_Term_MatchExpr_initK___closed__2;
                v___x_3007_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3006_, v_currMacroScope_2987_);
                lean_inc(v___x_3007_);
                v___x_3008_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3008_, 0, v_a_2996_);
                lean_ctor_set(v___x_3008_, 1, v___x_3005_);
                lean_ctor_set(v___x_3008_, 2, v___x_3007_);
                lean_ctor_set(v___x_3008_, 3, v___x_2982_);
                lean_inc(v_a_2984_);
                v___x_3009_ =
                    l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop(
                        v___x_3008_,
                        v___x_3004_,
                        v_a_2984_,
                        v_a_2980_,
                        v_a_2997_,
                    );
                if lean_obj_tag(v___x_3009_) == 0 {
                    v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
                    lean_inc(v_a_3010_);
                    v_a_3011_ = lean_ctor_get(v___x_3009_, 1);
                    lean_inc(v_a_3011_);
                    lean_dec_ref_known(v___x_3009_, 2);
                    v___x_3012_ = l_Lean_Elab_Term_MatchExpr_generate___lam__0(
                        v_ref_2988_,
                        v_a_2980_,
                        v_a_3011_,
                    );
                    v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
                    v_a_3014_ = lean_ctor_get(v___x_3012_, 1);
                    v_isSharedCheck_3099_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3099_ == 0 {
                        v___x_3016_ = v___x_3012_;
                        v_isShared_3017_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3014_);
                        lean_inc(v_a_3013_);
                        lean_dec(v___x_3012_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3007_);
                    lean_dec(v___x_3003_);
                    lean_del_object(v___x_2999_);
                    lean_del_object(v___x_2993_);
                    lean_dec(v_a_2984_);
                    lean_dec(v_elseAlt_2979_);
                    lean_dec(v_discr_2977_);
                    v_a_3100_ = lean_ctor_get(v___x_3009_, 0);
                    v_a_3101_ = lean_ctor_get(v___x_3009_, 1);
                    v_isSharedCheck_3108_ = (!lean_is_exclusive(v___x_3009_)) as u8;
                    if v_isSharedCheck_3108_ == 0 {
                        v___x_3103_ = v___x_3009_;
                        v_isShared_3104_ = v_isSharedCheck_3108_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3101_);
                        lean_inc(v_a_3100_);
                        lean_dec(v___x_3009_);
                        v___x_3103_ = lean_box(0);
                        v_isShared_3104_ = v_isSharedCheck_3108_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3018_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__0;
                v___x_3019_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg___closed__1;
                lean_inc(v_a_3013_);
                if v_isShared_3017_ == 0 {
                    lean_ctor_set_tag(v___x_3016_, 2);
                    lean_ctor_set(v___x_3016_, 1, v___x_3018_);
                    v___x_3021_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3018_);
                    v___x_3021_ = v_reuseFailAlloc_3098_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3022_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__18;
                v___x_3023_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__20;
                v___x_3024_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__22;
                lean_inc_n(v_a_3013_, 3);
                v___x_3025_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3025_, 0, v_a_3013_);
                lean_ctor_set(v___x_3025_, 1, v___x_3005_);
                lean_ctor_set(v___x_3025_, 2, v___x_3007_);
                lean_ctor_set(v___x_3025_, 3, v___x_2982_);
                v___x_3026_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3024_, v___x_3025_);
                v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
                v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__1;
                v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__2;
                if v_isShared_3000_ == 0 {
                    lean_ctor_set_tag(v___x_2999_, 2);
                    lean_ctor_set(v___x_2999_, 1, v___x_3029_);
                    lean_ctor_set(v___x_2999_, 0, v_a_3013_);
                    v___x_3031_ = v___x_2999_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3032_ = l_List_mapTR_loop___at___00Lean_Elab_Term_MatchExpr_toAlt_x3f_spec__0___closed__1;
                v___x_3033_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__0;
                lean_inc(v_a_3013_);
                if v_isShared_2994_ == 0 {
                    lean_ctor_set_tag(v___x_2993_, 2);
                    lean_ctor_set(v___x_2993_, 1, v___x_3033_);
                    lean_ctor_set(v___x_2993_, 0, v_a_3013_);
                    v___x_3035_ = v___x_2993_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_n(v_a_3013_, 23);
                v___x_3036_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3032_, v___x_3035_);
                v___x_3037_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3027_, v___x_3036_);
                v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__5;
                v___x_3039_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3039_, 0, v_a_3013_);
                lean_ctor_set(v___x_3039_, 1, v___x_3038_);
                v___x_3040_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_getParams___closed__2_once),
                    _init_l_Lean_Elab_Term_MatchExpr_getParams___closed__2,
                );
                v___x_3041_ = l_Lean_Elab_Term_MatchExpr_getParams___closed__3;
                lean_inc_n(v_currMacroScope_2987_, 2);
                lean_inc_n(v_quotContext_2986_, 2);
                v___x_3042_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3041_, v_currMacroScope_2987_);
                v___x_3043_ = l_Lean_Elab_Term_MatchExpr_generate___closed__2;
                v___x_3044_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3044_, 0, v_a_3013_);
                lean_ctor_set(v___x_3044_, 1, v___x_3040_);
                lean_ctor_set(v___x_3044_, 2, v___x_3042_);
                lean_ctor_set(v___x_3044_, 3, v___x_3043_);
                v___x_3045_ = l_Lean_Syntax_node2(v_a_3013_, v___x_3027_, v___x_3039_, v___x_3044_);
                v___x_3046_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__14);
                v___x_3047_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3047_, 0, v_a_3013_);
                lean_ctor_set(v___x_3047_, 1, v___x_3027_);
                lean_ctor_set(v___x_3047_, 2, v___x_3046_);
                v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__15;
                v___x_3049_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3049_, 0, v_a_3013_);
                lean_ctor_set(v___x_3049_, 1, v___x_3048_);
                lean_inc_ref_n(v___x_3047_, 4);
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
                v___x_3053_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3053_, 0, v_a_3013_);
                lean_ctor_set(v___x_3053_, 1, v___x_3052_);
                lean_inc_ref(v___x_3053_);
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
                v___x_3057_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3057_, 0, v_a_3013_);
                lean_ctor_set(v___x_3057_, 1, v___x_3056_);
                v___x_3058_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__13;
                v___x_3059_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__14;
                v___x_3060_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3060_, 0, v_a_3013_);
                lean_ctor_set(v___x_3060_, 1, v___x_3058_);
                v___x_3061_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop___closed__16;
                v___x_3062_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3061_, v___x_3047_);
                v___x_3063_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3063_, 0, v_a_3013_);
                lean_ctor_set(v___x_3063_, 1, v___x_3001_);
                lean_ctor_set(v___x_3063_, 2, v___x_3003_);
                lean_ctor_set(v___x_3063_, 3, v___x_2982_);
                v___x_3064_ = l_Lean_Syntax_node1(v_a_3013_, v___x_3024_, v___x_3063_);
                v___x_3065_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_MatchExpr_generate_loop_spec__0___redArg___closed__2;
                v___x_3066_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_generate___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_MatchExpr_generate___closed__4_once),
                    _init_l_Lean_Elab_Term_MatchExpr_generate___closed__4,
                );
                v___x_3067_ = l_Lean_Elab_Term_MatchExpr_generate___closed__6;
                v___x_3068_ =
                    l_Lean_addMacroScope(v_quotContext_2986_, v___x_3067_, v_currMacroScope_2987_);
                v___x_3069_ = l_Lean_Elab_Term_MatchExpr_generate___closed__9;
                v___x_3070_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3070_, 0, v_a_3013_);
                lean_ctor_set(v___x_3070_, 1, v___x_3066_);
                lean_ctor_set(v___x_3070_, 2, v___x_3068_);
                lean_ctor_set(v___x_3070_, 3, v___x_3069_);
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
                lean_inc_ref(v___x_3057_);
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
                lean_dec(v_a_2984_);
                if lean_obj_tag(v___x_3077_) == 0 {
                    v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
                    v_a_3079_ = lean_ctor_get(v___x_3077_, 1);
                    v_isSharedCheck_3086_ = (!lean_is_exclusive(v___x_3077_)) as u8;
                    if v_isSharedCheck_3086_ == 0 {
                        v___x_3081_ = v___x_3077_;
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3079_);
                        lean_inc(v_a_3078_);
                        lean_dec(v___x_3077_);
                        v___x_3081_ = lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_3087_ = lean_ctor_get(v___x_3077_, 0);
                    v_a_3088_ = lean_ctor_get(v___x_3077_, 1);
                    v_isSharedCheck_3095_ = (!lean_is_exclusive(v___x_3077_)) as u8;
                    if v_isSharedCheck_3095_ == 0 {
                        v___x_3090_ = v___x_3077_;
                        v_isShared_3091_ = v_isSharedCheck_3095_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3088_);
                        lean_inc(v_a_3087_);
                        lean_dec(v___x_3077_);
                        v___x_3090_ = lean_box(0);
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
                    v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3078_);
                    lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_a_3079_);
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
                    v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3087_);
                    lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3088_);
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
                    v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_a_3101_);
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
                    v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3111_);
                    lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_a_3112_);
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
    mut v_discr_3120_: *mut LeanObject,
    mut v_alts_3121_: *mut LeanObject,
    mut v_elseAlt_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v_a_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3125_: *mut LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Lean_Elab_Term_MatchExpr_generate(
        v_discr_3120_,
        v_alts_3121_,
        v_elseAlt_3122_,
        v_a_3123_,
        v_a_3124_,
    );
    lean_dec_ref(v_a_3123_);
    return v_res_3125_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(
    mut v_as_3126_: *mut LeanObject,
    mut v_as_x27_3127_: *mut LeanObject,
    mut v_b_3128_: *mut LeanObject,
    mut v_a_3129_: *mut LeanObject,
    mut v___y_3130_: *mut LeanObject,
    mut v___y_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___redArg(
        v_as_x27_3127_,
        v_b_3128_,
        v___y_3130_,
        v___y_3131_,
    );
    return v___x_3132_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1___boxed(
    mut v_as_3133_: *mut LeanObject,
    mut v_as_x27_3134_: *mut LeanObject,
    mut v_b_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3139_: *mut LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_MatchExpr_generate_spec__1(
        v_as_3133_,
        v_as_x27_3134_,
        v_b_3135_,
        v_a_3136_,
        v___y_3137_,
        v___y_3138_,
    );
    lean_dec_ref(v___y_3137_);
    lean_dec(v_as_x27_3134_);
    lean_dec(v_as_3133_);
    return v_res_3139_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
    mut v_x_3141_: *mut LeanObject,
    mut v_x_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3141_) == 0 {
                    v___x_3145_ = l_List_reverse___redArg(v_x_3142_);
                    v___x_3146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3146_, 0, v___x_3145_);
                    lean_ctor_set(v___x_3146_, 1, v___y_3144_);
                    return v___x_3146_;
                } else {
                    v_head_3147_ = lean_ctor_get(v_x_3141_, 0);
                    v_tail_3148_ = lean_ctor_get(v_x_3141_, 1);
                    v_isSharedCheck_3174_ = (!lean_is_exclusive(v_x_3141_)) as u8;
                    if v_isSharedCheck_3174_ == 0 {
                        v___x_3150_ = v_x_3141_;
                        v_isShared_3151_ = v_isSharedCheck_3174_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3148_);
                        lean_inc(v_head_3147_);
                        lean_dec(v_x_3141_);
                        v___x_3150_ = lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3174_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_3147_);
                v___x_3159_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f(v_head_3147_);
                if lean_obj_tag(v___x_3159_) == 1 {
                    lean_dec(v_head_3147_);
                    v_val_3160_ = lean_ctor_get(v___x_3159_, 0);
                    lean_inc(v_val_3160_);
                    lean_dec_ref_known(v___x_3159_, 1);
                    v_a_3153_ = v_val_3160_;
                    v_a_3154_ = v___y_3144_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_3159_);
                    v___x_3161_ =
                        l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0___closed__0;
                    v___x_3162_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_head_3147_,
                        v___x_3161_,
                        v___y_3143_,
                        v___y_3144_,
                    );
                    lean_dec(v_head_3147_);
                    if lean_obj_tag(v___x_3162_) == 0 {
                        v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
                        lean_inc(v_a_3163_);
                        v_a_3164_ = lean_ctor_get(v___x_3162_, 1);
                        lean_inc(v_a_3164_);
                        lean_dec_ref_known(v___x_3162_, 2);
                        v_a_3153_ = v_a_3163_;
                        v_a_3154_ = v_a_3164_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_3150_);
                        lean_dec(v_tail_3148_);
                        lean_dec(v_x_3142_);
                        v_a_3165_ = lean_ctor_get(v___x_3162_, 0);
                        v_a_3166_ = lean_ctor_get(v___x_3162_, 1);
                        v_isSharedCheck_3173_ = (!lean_is_exclusive(v___x_3162_)) as u8;
                        if v_isSharedCheck_3173_ == 0 {
                            v___x_3168_ = v___x_3162_;
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3166_);
                            lean_inc(v_a_3165_);
                            lean_dec(v___x_3162_);
                            v___x_3168_ = lean_box(0);
                            v_isShared_3169_ = v_isSharedCheck_3173_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_3151_ == 0 {
                    lean_ctor_set(v___x_3150_, 1, v_x_3142_);
                    lean_ctor_set(v___x_3150_, 0, v_a_3153_);
                    v___x_3156_ = v___x_3150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3153_);
                    lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_x_3142_);
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
                    v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3165_);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3166_);
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
    mut v_x_3175_: *mut LeanObject,
    mut v_x_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
        v_x_3175_,
        v_x_3176_,
        v___y_3177_,
        v___y_3178_,
    );
    lean_dec_ref(v___y_3177_);
    return v_res_3179_;
}
pub unsafe fn l_Lean_Elab_Term_MatchExpr_main(
    mut v_discr_3181_: *mut LeanObject,
    mut v_alts_3182_: *mut LeanObject,
    mut v_elseAlt_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3186_ = lean_array_to_list(v_alts_3182_);
                v___x_3187_ = lean_box(0);
                v___x_3188_ = l_List_mapM_loop___at___00Lean_Elab_Term_MatchExpr_main_spec__0(
                    v___x_3186_,
                    v___x_3187_,
                    v_a_3184_,
                    v_a_3185_,
                );
                if lean_obj_tag(v___x_3188_) == 0 {
                    v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
                    lean_inc(v_a_3189_);
                    v_a_3190_ = lean_ctor_get(v___x_3188_, 1);
                    lean_inc(v_a_3190_);
                    lean_dec_ref_known(v___x_3188_, 2);
                    lean_inc(v_elseAlt_3183_);
                    v___x_3191_ = l_Lean_Elab_Term_MatchExpr_toElseAlt_x3f(v_elseAlt_3183_);
                    if lean_obj_tag(v___x_3191_) == 1 {
                        lean_dec(v_elseAlt_3183_);
                        v_val_3192_ = lean_ctor_get(v___x_3191_, 0);
                        lean_inc(v_val_3192_);
                        lean_dec_ref_known(v___x_3191_, 1);
                        v___x_3193_ = l_Lean_Elab_Term_MatchExpr_generate(
                            v_discr_3181_,
                            v_a_3189_,
                            v_val_3192_,
                            v_a_3184_,
                            v_a_3190_,
                        );
                        return v___x_3193_;
                    } else {
                        lean_dec(v___x_3191_);
                        lean_dec(v_a_3189_);
                        lean_dec(v_discr_3181_);
                        v___x_3194_ = l_Lean_Elab_Term_MatchExpr_main___closed__0;
                        v___x_3195_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_elseAlt_3183_,
                            v___x_3194_,
                            v_a_3184_,
                            v_a_3190_,
                        );
                        lean_dec(v_elseAlt_3183_);
                        return v___x_3195_;
                    }
                } else {
                    lean_dec(v_elseAlt_3183_);
                    lean_dec(v_discr_3181_);
                    v_a_3196_ = lean_ctor_get(v___x_3188_, 0);
                    v_a_3197_ = lean_ctor_get(v___x_3188_, 1);
                    v_isSharedCheck_3204_ = (!lean_is_exclusive(v___x_3188_)) as u8;
                    if v_isSharedCheck_3204_ == 0 {
                        v___x_3199_ = v___x_3188_;
                        v_isShared_3200_ = v_isSharedCheck_3204_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3197_);
                        lean_inc(v_a_3196_);
                        lean_dec(v___x_3188_);
                        v___x_3199_ = lean_box(0);
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
                    v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3196_);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_a_3197_);
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
    mut v_discr_3205_: *mut LeanObject,
    mut v_alts_3206_: *mut LeanObject,
    mut v_elseAlt_3207_: *mut LeanObject,
    mut v_a_3208_: *mut LeanObject,
    mut v_a_3209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3210_: *mut LeanObject = core::ptr::null_mut();
    v_res_3210_ = l_Lean_Elab_Term_MatchExpr_main(
        v_discr_3205_,
        v_alts_3206_,
        v_elseAlt_3207_,
        v_a_3208_,
        v_a_3209_,
    );
    lean_dec_ref(v_a_3208_);
    return v_res_3210_;
}
pub unsafe fn l_Lean_Elab_Term_expandMatchExpr(
    mut v_stx_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: u8 = 0;
    v___x_3220_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
    lean_inc(v_stx_3217_);
    v___x_3221_ = l_Lean_Syntax_isOfKind(v_stx_3217_, v___x_3220_);
    if v___x_3221_ == 0 {
        let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_3217_);
        v___x_3222_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3219_);
        return v___x_3222_;
    } else {
        let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
        let mut v_discr_3225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
        v___x_3223_ = lean_unsigned_to_nat(0);
        v___x_3224_ = lean_unsigned_to_nat(1);
        v_discr_3225_ = l_Lean_Syntax_getArg(v_stx_3217_, v___x_3224_);
        v___x_3226_ = lean_unsigned_to_nat(3);
        v___x_3227_ = l_Lean_Syntax_getArg(v_stx_3217_, v___x_3226_);
        lean_dec(v_stx_3217_);
        v___x_3228_ = l_Lean_Syntax_getArg(v___x_3227_, v___x_3223_);
        v___x_3229_ = l_Lean_Syntax_getArgs(v___x_3228_);
        lean_dec(v___x_3228_);
        v___x_3230_ = l_Lean_Syntax_getArg(v___x_3227_, v___x_3224_);
        lean_dec(v___x_3227_);
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
    mut v_stx_3232_: *mut LeanObject,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3235_: *mut LeanObject = core::ptr::null_mut();
    v_res_3235_ = l_Lean_Elab_Term_expandMatchExpr(v_stx_3232_, v_a_3233_, v_a_3234_);
    lean_dec_ref(v_a_3233_);
    return v_res_3235_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1()
-> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_Elab_macroAttribute;
    v___x_3244_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
    v___x_3245_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1;
    v___x_3246_ = lean_alloc_closure(
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
    mut v_a_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3249_: *mut LeanObject = core::ptr::null_mut();
    v_res_3249_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
    return v_res_3249_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3()
-> *mut LeanObject {
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    v___x_3276_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1___closed__1;
    v___x_3277_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___closed__6;
    v___x_3278_ = l_Lean_addBuiltinDeclarationRanges(v___x_3276_, v___x_3277_);
    return v___x_3278_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3___boxed(
    mut v_a_3279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3280_: *mut LeanObject = core::ptr::null_mut();
    v_res_3280_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
    return v_res_3280_;
}
pub unsafe fn l_Lean_Elab_Term_expandLetExpr(
    mut v_stx_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: u8 = 0;
    v___x_3300_ = l_Lean_Elab_Term_expandLetExpr___closed__1;
    lean_inc(v_stx_3297_);
    v___x_3301_ = l_Lean_Syntax_isOfKind(v_stx_3297_, v___x_3300_);
    if v___x_3301_ == 0 {
        let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_3297_);
        v___x_3302_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3299_);
        return v___x_3302_;
    } else {
        let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3306_: u8 = 0;
        v___x_3303_ = lean_unsigned_to_nat(1);
        v___x_3304_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3303_);
        v___x_3305_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__5;
        lean_inc(v___x_3304_);
        v___x_3306_ = l_Lean_Syntax_isOfKind(v___x_3304_, v___x_3305_);
        if v___x_3306_ == 0 {
            let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3304_);
            lean_dec(v_stx_3297_);
            v___x_3307_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3299_);
            return v___x_3307_;
        } else {
            let mut v_ref_3308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3315_: u8 = 0;
            let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
            v_ref_3308_ = lean_ctor_get(v_a_3298_, 5);
            v___x_3309_ = lean_unsigned_to_nat(3);
            v___x_3310_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3309_);
            v___x_3311_ = lean_unsigned_to_nat(5);
            v___x_3312_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3311_);
            v___x_3313_ = lean_unsigned_to_nat(7);
            v___x_3314_ = l_Lean_Syntax_getArg(v_stx_3297_, v___x_3313_);
            lean_dec(v_stx_3297_);
            v___x_3315_ = 0;
            v___x_3316_ = l_Lean_SourceInfo_fromRef(v_ref_3308_, v___x_3315_);
            v___x_3317_ = l_Lean_Elab_Term_expandMatchExpr___closed__1;
            v___x_3318_ = l_Lean_Elab_Term_expandLetExpr___closed__2;
            lean_inc_n(v___x_3316_, 10);
            v___x_3319_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3319_, 0, v___x_3316_);
            lean_ctor_set(v___x_3319_, 1, v___x_3318_);
            v___x_3320_ = l_Lean_Elab_Term_expandLetExpr___closed__3;
            v___x_3321_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3321_, 0, v___x_3316_);
            lean_ctor_set(v___x_3321_, 1, v___x_3320_);
            v___x_3322_ = l_Lean_Elab_Term_expandLetExpr___closed__5;
            v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_MatchExpr_getParams_spec__0_spec__0___closed__4;
            v___x_3324_ = l_Lean_Elab_Term_MatchExpr_toAlt_x3f___closed__1;
            v___x_3325_ = l_Lean_Elab_Term_expandLetExpr___closed__6;
            v___x_3326_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3326_, 0, v___x_3316_);
            lean_ctor_set(v___x_3326_, 1, v___x_3325_);
            v___x_3327_ = l_Lean_Elab_Term_expandLetExpr___closed__7;
            v___x_3328_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3328_, 0, v___x_3316_);
            lean_ctor_set(v___x_3328_, 1, v___x_3327_);
            lean_inc_ref(v___x_3328_);
            lean_inc_ref(v___x_3326_);
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
            v___x_3334_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_3334_, 0, v___x_3316_);
            lean_ctor_set(v___x_3334_, 1, v___x_3333_);
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
            v___x_3339_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3339_, 0, v___x_3338_);
            lean_ctor_set(v___x_3339_, 1, v_a_3299_);
            return v___x_3339_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_expandLetExpr___boxed(
    mut v_stx_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3343_: *mut LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Lean_Elab_Term_expandLetExpr(v_stx_3340_, v_a_3341_, v_a_3342_);
    lean_dec_ref(v_a_3341_);
    return v_res_3343_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1()
-> *mut LeanObject {
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Lean_Elab_macroAttribute;
    v___x_3352_ = l_Lean_Elab_Term_expandLetExpr___closed__1;
    v___x_3353_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1;
    v___x_3354_ = lean_alloc_closure(
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
    mut v_a_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3()
-> *mut LeanObject {
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    v___x_3384_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1___closed__1;
    v___x_3385_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___closed__6;
    v___x_3386_ = l_Lean_addBuiltinDeclarationRanges(v___x_3384_, v___x_3385_);
    return v___x_3386_;
}
pub unsafe fn l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3___boxed(
    mut v_a_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
    return v_res_3388_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandMatchExpr___regBuiltin_Lean_Elab_Term_expandMatchExpr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MatchExpr_0__Lean_Elab_Term_expandLetExpr___regBuiltin_Lean_Elab_Term_expandLetExpr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MatchExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MatchExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MatchExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_MatchExpr(builtin);
}

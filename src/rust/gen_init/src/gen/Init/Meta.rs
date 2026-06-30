// Lean compiler output
// Module: Init.Meta
// Imports: Init.Meta.Defs Init.Meta.Defs Init.Syntax
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_sub, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Parser_Tactic_appendConfig,
    l_Lean_Parser_Tactic_getConfigItems, l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit,
    l_Lean_Syntax_mkSynthetic, l_Lean_evalPrec, l_Lean_evalPrio, runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getKind, l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_Syntax_setKind,
    l_Lean_addMacroScope, l_Lean_mkAtomFrom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Init::Tactics::{
    l_Lean_Parser_Tactic_discharger, l_Lean_Parser_Tactic_location, l_Lean_Parser_Tactic_optConfig,
    l_Lean_Parser_Tactic_rwRuleSeq, l_Lean_Parser_Tactic_simpErase, l_Lean_Parser_Tactic_simpLemma,
    l_Lean_Parser_Tactic_simpStar,
};
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 100, 100, 80, 114, 101, 99, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__3_value) as *mut leanh::LeanObject,16362184326174426309 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 117, 98, 80, 114, 101, 99, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__0_value) as *mut leanh::LeanObject,6194922959992300182 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__0_value: leanh::LeanStringObject<15> =
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
            116, 101, 114, 109, 69, 118, 97, 108, 95, 112, 114, 101, 99, 95, 0,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_termEval__prec___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean_termEval__prec___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__0_value)
                as *mut leanh::LeanObject,
            18375174615983841591 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_Lean_termEval__prec___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__4_value: leanh::LeanStringObject<11> =
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
        m_data: [101, 118, 97, 108, 95, 112, 114, 101, 99, 32, 0],
    };
static mut l_Lean_termEval__prec___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__6_value: leanh::LeanStringObject<5> =
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
        m_data: [112, 114, 101, 99, 0],
    };
static mut l_Lean_termEval__prec___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__6_value)
                as *mut leanh::LeanObject,
            6272524648685798834 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prec___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prec___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_termEval__prec__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 100, 100, 80, 114, 105, 111, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__0_value) as *mut leanh::LeanObject,11551461841016642050 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 117, 98, 80, 114, 105, 111, 0]};
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__0_value) as *mut leanh::LeanObject,7350253384150420525 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__0_value: leanh::LeanStringObject<15> =
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
            116, 101, 114, 109, 69, 118, 97, 108, 95, 112, 114, 105, 111, 95, 0,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_termEval__prio___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean_termEval__prio___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__0_value)
                as *mut leanh::LeanObject,
            12596184397761583873 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__2_value: leanh::LeanStringObject<11> =
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
        m_data: [101, 118, 97, 108, 95, 112, 114, 105, 111, 32, 0],
    };
static mut l_Lean_termEval__prio___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [112, 114, 105, 111, 0],
    };
static mut l_Lean_termEval__prio___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__4_value)
                as *mut leanh::LeanObject,
            17836958171642591098 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__5_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termEval__prio___00__closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_termEval__prio___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_termEval__prio__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termEval__prio___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 97, 99, 116, 105, 99, 69, 114, 119, 95, 95, 95, 0],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__1_value)
            as *mut leanh::LeanObject,
        15239434151197732561 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [101, 114, 119, 0],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__4_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__3_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
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
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__7_value)
            as *mut leanh::LeanObject,
        18170484695678750185 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_tacticErw_______00__closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_tacticErw______: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value) as *mut leanh::LeanObject,3488656302031949961 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 119, 83, 101, 113, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__2_value) as *mut leanh::LeanObject,11075965128531316786 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [114, 119, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__5_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__8_value) as *mut leanh::LeanObject,10138443044734372301 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__10_value) as *mut leanh::LeanObject,13577612981047608199 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13_value) as *mut leanh::LeanObject,9886976150145685689 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__18_value) as *mut leanh::LeanObject,14183307858573822893 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value) as *mut leanh::LeanObject,9666231177748665885 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__24_value) as *mut leanh::LeanObject,13340093926952294564 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21_value) as *mut leanh::LeanObject,609174137020324014 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__25_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__27_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__26_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 105, 109, 112, 65, 108, 108, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_simpAllKind___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__0_value)
                as *mut leanh::LeanObject,
            13293467073621420413 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__2_value)
                as *mut leanh::LeanObject,
            4024150434455327032 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [32, 40, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__6_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [97, 108, 108, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__6_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__10_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__11_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__13_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__13_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__16_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllKind___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllKind___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__18_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_simpAllKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [100, 115, 105, 109, 112, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_dsimpKind___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__0_value)
                as *mut leanh::LeanObject,
            836278672747009031 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__5_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpKind___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpKind___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__9_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_dsimpKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        100, 101, 99, 108, 97, 114, 101, 83, 105, 109, 112, 76, 105, 107, 101, 84, 97, 99, 116,
        105, 99, 0,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__0_value)
            as *mut leanh::LeanObject,
        8130572857906175311 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
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
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__2_value)
            as *mut leanh::LeanObject,
        3961966953292576997 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        100, 101, 99, 108, 97, 114, 101, 95, 115, 105, 109, 112, 95, 108, 105, 107, 101, 95, 116,
        97, 99, 116, 105, 99, 0,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value:
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
    m_data: [111, 114, 101, 108, 115, 101, 0],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__9_value)
            as *mut leanh::LeanObject,
        393173242845875278 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__18_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__14_value)
            as *mut leanh::LeanObject,
        2214559063752339918 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 112, 83, 112, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__16_value)
            as *mut leanh::LeanObject,
        17761616517784022991 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
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
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__21_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__22_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__20_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__23_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__24_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__26_value)
            as *mut leanh::LeanObject,
        9232979286016572671 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__25_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__28_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termEval__prec___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__29_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_declareSimpLikeTactic: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 99, 114, 111, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 112, 97, 110, 100, 83, 105, 109, 112, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14_value) as *mut leanh::LeanObject,13686763388568798338 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20_value) as *mut leanh::LeanObject,14665357199263665561 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [115, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value) as *mut leanh::LeanObject,5370976759840893899 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 76, 101, 116, 65, 114, 114, 111, 119, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 73, 100, 68, 101, 99, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 102, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37_value) as *mut leanh::LeanObject,1529402619103148481 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 121, 110, 97, 109, 105, 99, 81, 117, 111, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 40, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 111, 76, 101, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 46, 115, 101, 116, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 101, 116, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value) as *mut leanh::LeanObject,5370976759840893899 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__52_value) as *mut leanh::LeanObject,6947020359086245130 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 46, 115, 101, 116, 65, 114, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 101, 116, 65, 114, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value) as *mut leanh::LeanObject,5370976759840893899 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__56_value) as *mut leanh::LeanObject,17601334059161162291 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__58_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__63_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 107, 65, 116, 111, 109, 70, 114, 111, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67_value) as *mut leanh::LeanObject,9311286265720571996 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__70_value) as *mut leanh::LeanObject,17746073143502587047 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 97, 110, 111, 110, 105, 99, 97, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74_value) as *mut leanh::LeanObject,11910749745948107258 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__13_value) as *mut leanh::LeanObject,6560861498103128555 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__79_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllKind___closed__13_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__80_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__81_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [49, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 112, 112, 101, 110, 100, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84_value) as *mut leanh::LeanObject,2543489118292638419 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 46, 109, 107, 83, 121, 110, 116, 104, 101, 116, 105, 99, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 107, 83, 121, 110, 116, 104, 101, 116, 105, 99, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26_value) as *mut leanh::LeanObject,5370976759840893899 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__89_value) as *mut leanh::LeanObject,390047082954570528 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 82, 101, 116, 117, 114, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 116, 117, 114, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 111, 109, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__2_value) as *mut leanh::LeanObject,6376237424612349584 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 97, 116, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__4_value) as *mut leanh::LeanObject,14125453249386077023 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0_value) as *mut leanh::LeanObject,13390569275765148312 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 120, 95, 63, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__8_value) as *mut leanh::LeanObject,14916367973757185555 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61_value) as *mut leanh::LeanObject,14182491107802134955 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value) as *mut leanh::LeanObject,9696601259044513016 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11_value) as *mut leanh::LeanObject,5158953184651098857 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [110, 111, 110, 82, 101, 115, 101, 114, 118, 101, 100, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__2_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__16_value) as *mut leanh::LeanObject,16345582273613418198 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [38, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [34, 32, 111, 110, 108, 121, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [34, 32, 91, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 120, 95, 44, 42, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__21_value) as *mut leanh::LeanObject,17404491096665796008 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 120, 95, 60, 124, 62, 95, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__23_value) as *mut leanh::LeanObject,7409751955955409350 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 83, 116, 97, 114, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value) as *mut leanh::LeanObject,119038878794744804 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25_value) as *mut leanh::LeanObject,2669418402702632573 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 124, 62, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 69, 114, 97, 115, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value) as *mut leanh::LeanObject,12014993282382919369 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30_value) as *mut leanh::LeanObject,11353779426050775256 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value) as *mut leanh::LeanObject,5678799681970723599 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34_value) as *mut leanh::LeanObject,7383208167966365478 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 42, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [34, 93, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value) as *mut leanh::LeanObject,11490083008225922661 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40_value) as *mut leanh::LeanObject,1767494567867404924 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44_value) as *mut leanh::LeanObject,16145843736367156323 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__47_value) as *mut leanh::LeanObject,11323065835382012354 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__2_value) as *mut leanh::LeanObject,15739350005989697343 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpKind___closed__2_value) as *mut leanh::LeanObject,5511199417188169206 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__53_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [34, 100, 115, 105, 109, 112, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56_value) as *mut leanh::LeanObject,2812521669163367463 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 65, 108, 108, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value) as *mut leanh::LeanObject,4034256009637811484 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58_value) as *mut leanh::LeanObject,17985617252278808837 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__62_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [34, 115, 105, 109, 112, 95, 97, 108, 108, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value) as *mut leanh::LeanObject,13994041031692860867 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67_value) as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65_value) as *mut leanh::LeanObject,12783917532758215986 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__69_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [34, 115, 105, 109, 112, 34, 0]};
static mut l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value: leanh::LeanStringObject<
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
        115, 105, 109, 112, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__0_value)
                as *mut leanh::LeanObject,
            17342550436400123219 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 105, 109, 112, 33, 32, 0],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value: leanh::LeanStringObject<
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
    m_data: [32, 111, 110, 108, 121, 0],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__7_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 91, 0],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__12_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__15_value: leanh::LeanStringObject<
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
    m_data: [44, 0],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__17_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAutoUnfold___closed__20_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAutoUnfold___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpAutoUnfold: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0]};
static mut l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value) as *mut leanh::LeanObject,10924163692938741069 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpArith___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 65, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_simpArith___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__0_value)
                as *mut leanh::LeanObject,
            14480302902855741354 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpArith___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [115, 105, 109, 112, 95, 97, 114, 105, 116, 104, 32, 0],
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpArith___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArith___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpArith___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArith___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArith___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArith___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArith___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArith___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArith___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpArith: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpArithBang___closed__0_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
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
        115, 105, 109, 112, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0,
    ],
};
static mut l_Lean_Parser_Tactic_simpArithBang___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_simpArithBang___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__0_value)
                as *mut leanh::LeanObject,
            4672287204283619115 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpArithBang___closed__2_value: leanh::LeanStringObject<
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
    m_data: [115, 105, 109, 112, 95, 97, 114, 105, 116, 104, 33, 32, 0],
};
static mut l_Lean_Parser_Tactic_simpArithBang___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpArithBang___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpArithBang___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpArithBang___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArithBang___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArithBang___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArithBang___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArithBang___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpArithBang___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpArithBang___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpArithBang: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        115, 105, 109, 112, 65, 108, 108, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__0_value)
            as *mut leanh::LeanObject,
        10659525765844864087 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 105, 109, 112, 95, 97, 108, 108, 33, 32, 0],
};
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpAllAutoUnfold: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 95, 97, 108, 108, 0]};
static mut l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3__value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllArith___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [115, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 0],
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_simpAllArith___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__0_value)
                as *mut leanh::LeanObject,
            3392380392473414360 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllArith___closed__2_value: leanh::LeanStringObject<15> =
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
            115, 105, 109, 112, 95, 97, 108, 108, 95, 97, 114, 105, 116, 104, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllArith___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArith___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAllArith___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArith___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArith___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArith___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArith___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArith___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpAllArith: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
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
        115, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__0_value)
            as *mut leanh::LeanObject,
        3546702534615090220 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
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
        115, 105, 109, 112, 95, 97, 108, 108, 95, 97, 114, 105, 116, 104, 33, 0,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_simpAllArithBang___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_simpAllArithBang___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_simpAllArithBang___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_simpAllArithBang: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
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
        100, 115, 105, 109, 112, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_tacticErw_______00__closed__0_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__0_value)
                as *mut leanh::LeanObject,
            18010431552314929788 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 115, 105, 109, 112, 33, 32, 0],
};
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_dsimpAutoUnfold: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1(
    mut v_x_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
    mut v_a_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2423_: u8 = 0;
    let mut v_a_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2428_: u8 = 0;
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2437_: u8 = 0;
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__4;
                leanh::lean_inc(v_x_2396_);
                v___x_2400_ = l_Lean_Syntax_isOfKind(v_x_2396_, v___x_2399_);
                if v___x_2400_ == 0 {
                    leanh::lean_dec(v_x_2396_);
                    v___x_2401_ = leanh::lean_box(1);
                    v___x_2402_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2402_, 0, v___x_2401_);
                    leanh::lean_ctor_set(v___x_2402_, 1, v_a_2398_);
                    return v___x_2402_;
                } else {
                    v___x_2403_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2404_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2403_);
                    v___x_2405_ = l_Lean_evalPrec(v___x_2404_, v_a_2397_, v_a_2398_);
                    if leanh::lean_obj_tag(v___x_2405_) == 0 {
                        v_a_2406_ = leanh::lean_ctor_get(v___x_2405_, 0);
                        leanh::lean_inc(v_a_2406_);
                        v_a_2407_ = leanh::lean_ctor_get(v___x_2405_, 1);
                        leanh::lean_inc(v_a_2407_);
                        leanh::lean_dec_ref_known(v___x_2405_, 2);
                        v___x_2408_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2409_ = l_Lean_Syntax_getArg(v_x_2396_, v___x_2408_);
                        leanh::lean_dec(v_x_2396_);
                        v___x_2410_ = l_Lean_evalPrec(v___x_2409_, v_a_2397_, v_a_2407_);
                        if leanh::lean_obj_tag(v___x_2410_) == 0 {
                            v_a_2411_ = leanh::lean_ctor_get(v___x_2410_, 0);
                            v_a_2412_ = leanh::lean_ctor_get(v___x_2410_, 1);
                            v_isSharedCheck_2423_ =
                                (!leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2423_ == 0 {
                                v___x_2414_ = v___x_2410_;
                                v_isShared_2415_ = v_isSharedCheck_2423_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2412_);
                                leanh::lean_inc(v_a_2411_);
                                leanh::lean_dec(v___x_2410_);
                                v___x_2414_ = leanh::lean_box(0);
                                v_isShared_2415_ = v_isSharedCheck_2423_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2406_);
                            v_a_2424_ = leanh::lean_ctor_get(v___x_2410_, 0);
                            v_a_2425_ = leanh::lean_ctor_get(v___x_2410_, 1);
                            v_isSharedCheck_2432_ =
                                (!leanh::lean_is_exclusive(v___x_2410_)) as u8;
                            if v_isSharedCheck_2432_ == 0 {
                                v___x_2427_ = v___x_2410_;
                                v_isShared_2428_ = v_isSharedCheck_2432_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2425_);
                                leanh::lean_inc(v_a_2424_);
                                leanh::lean_dec(v___x_2410_);
                                v___x_2427_ = leanh::lean_box(0);
                                v_isShared_2428_ = v_isSharedCheck_2432_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_2396_);
                        v_a_2433_ = leanh::lean_ctor_get(v___x_2405_, 0);
                        v_a_2434_ = leanh::lean_ctor_get(v___x_2405_, 1);
                        v_isSharedCheck_2441_ =
                            (!leanh::lean_is_exclusive(v___x_2405_)) as u8;
                        if v_isSharedCheck_2441_ == 0 {
                            v___x_2436_ = v___x_2405_;
                            v_isShared_2437_ = v_isSharedCheck_2441_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2434_);
                            leanh::lean_inc(v_a_2433_);
                            leanh::lean_dec(v___x_2405_);
                            v___x_2436_ = leanh::lean_box(0);
                            v_isShared_2437_ = v_isSharedCheck_2441_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2416_ = lean_nat_add(v_a_2406_, v_a_2411_);
                leanh::lean_dec(v_a_2411_);
                leanh::lean_dec(v_a_2406_);
                v___x_2417_ = l_Nat_reprFast(v___x_2416_);
                v___x_2418_ = leanh::lean_box(2);
                v___x_2419_ = l_Lean_Syntax_mkNumLit(v___x_2417_, v___x_2418_);
                if v_isShared_2415_ == 0 {
                    leanh::lean_ctor_set(v___x_2414_, 0, v___x_2419_);
                    v___x_2421_ = v___x_2414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_a_2412_);
                    v___x_2421_ = v_reuseFailAlloc_2422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2421_;
            }
            3 => {
                if v_isShared_2428_ == 0 {
                    v___x_2430_ = v___x_2427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_a_2425_);
                    v___x_2430_ = v_reuseFailAlloc_2431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2430_;
            }
            5 => {
                if v_isShared_2437_ == 0 {
                    v___x_2439_ = v___x_2436_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2440_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_a_2434_);
                    v___x_2439_ = v_reuseFailAlloc_2440_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___boxed(
    mut v_x_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2445_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1(
        v_x_2442_, v_a_2443_, v_a_2444_,
    );
    leanh::lean_dec_ref(v_a_2443_);
    return v_res_2445_;
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(
    mut v_x_2452_: *mut leanh::LeanObject,
    mut v_a_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut v_a_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_a_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2493_: u8 = 0;
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2455_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___closed__1;
                leanh::lean_inc(v_x_2452_);
                v___x_2456_ = l_Lean_Syntax_isOfKind(v_x_2452_, v___x_2455_);
                if v___x_2456_ == 0 {
                    leanh::lean_dec(v_x_2452_);
                    v___x_2457_ = leanh::lean_box(1);
                    v___x_2458_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2458_, 0, v___x_2457_);
                    leanh::lean_ctor_set(v___x_2458_, 1, v_a_2454_);
                    return v___x_2458_;
                } else {
                    v___x_2459_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2460_ = l_Lean_Syntax_getArg(v_x_2452_, v___x_2459_);
                    v___x_2461_ = l_Lean_evalPrec(v___x_2460_, v_a_2453_, v_a_2454_);
                    if leanh::lean_obj_tag(v___x_2461_) == 0 {
                        v_a_2462_ = leanh::lean_ctor_get(v___x_2461_, 0);
                        leanh::lean_inc(v_a_2462_);
                        v_a_2463_ = leanh::lean_ctor_get(v___x_2461_, 1);
                        leanh::lean_inc(v_a_2463_);
                        leanh::lean_dec_ref_known(v___x_2461_, 2);
                        v___x_2464_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2465_ = l_Lean_Syntax_getArg(v_x_2452_, v___x_2464_);
                        leanh::lean_dec(v_x_2452_);
                        v___x_2466_ = l_Lean_evalPrec(v___x_2465_, v_a_2453_, v_a_2463_);
                        if leanh::lean_obj_tag(v___x_2466_) == 0 {
                            v_a_2467_ = leanh::lean_ctor_get(v___x_2466_, 0);
                            v_a_2468_ = leanh::lean_ctor_get(v___x_2466_, 1);
                            v_isSharedCheck_2479_ =
                                (!leanh::lean_is_exclusive(v___x_2466_)) as u8;
                            if v_isSharedCheck_2479_ == 0 {
                                v___x_2470_ = v___x_2466_;
                                v_isShared_2471_ = v_isSharedCheck_2479_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2468_);
                                leanh::lean_inc(v_a_2467_);
                                leanh::lean_dec(v___x_2466_);
                                v___x_2470_ = leanh::lean_box(0);
                                v_isShared_2471_ = v_isSharedCheck_2479_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2462_);
                            v_a_2480_ = leanh::lean_ctor_get(v___x_2466_, 0);
                            v_a_2481_ = leanh::lean_ctor_get(v___x_2466_, 1);
                            v_isSharedCheck_2488_ =
                                (!leanh::lean_is_exclusive(v___x_2466_)) as u8;
                            if v_isSharedCheck_2488_ == 0 {
                                v___x_2483_ = v___x_2466_;
                                v_isShared_2484_ = v_isSharedCheck_2488_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2481_);
                                leanh::lean_inc(v_a_2480_);
                                leanh::lean_dec(v___x_2466_);
                                v___x_2483_ = leanh::lean_box(0);
                                v_isShared_2484_ = v_isSharedCheck_2488_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_2452_);
                        v_a_2489_ = leanh::lean_ctor_get(v___x_2461_, 0);
                        v_a_2490_ = leanh::lean_ctor_get(v___x_2461_, 1);
                        v_isSharedCheck_2497_ =
                            (!leanh::lean_is_exclusive(v___x_2461_)) as u8;
                        if v_isSharedCheck_2497_ == 0 {
                            v___x_2492_ = v___x_2461_;
                            v_isShared_2493_ = v_isSharedCheck_2497_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2490_);
                            leanh::lean_inc(v_a_2489_);
                            leanh::lean_dec(v___x_2461_);
                            v___x_2492_ = leanh::lean_box(0);
                            v_isShared_2493_ = v_isSharedCheck_2497_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2472_ = lean_nat_sub(v_a_2462_, v_a_2467_);
                leanh::lean_dec(v_a_2467_);
                leanh::lean_dec(v_a_2462_);
                v___x_2473_ = l_Nat_reprFast(v___x_2472_);
                v___x_2474_ = leanh::lean_box(2);
                v___x_2475_ = l_Lean_Syntax_mkNumLit(v___x_2473_, v___x_2474_);
                if v_isShared_2471_ == 0 {
                    leanh::lean_ctor_set(v___x_2470_, 0, v___x_2475_);
                    v___x_2477_ = v___x_2470_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2468_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2477_;
            }
            3 => {
                if v_isShared_2484_ == 0 {
                    v___x_2486_ = v___x_2483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2481_);
                    v___x_2486_ = v_reuseFailAlloc_2487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2486_;
            }
            5 => {
                if v_isShared_2493_ == 0 {
                    v___x_2495_ = v___x_2492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_a_2490_);
                    v___x_2495_ = v_reuseFailAlloc_2496_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1___boxed(
    mut v_x_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrec__1(
        v_x_2498_, v_a_2499_, v_a_2500_,
    );
    leanh::lean_dec_ref(v_a_2499_);
    return v_res_2501_;
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(
    mut v_x_2527_: *mut leanh::LeanObject,
    mut v_a_2528_: *mut leanh::LeanObject,
    mut v_a_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v_a_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2530_ = l_Lean_termEval__prec___00__closed__1;
                leanh::lean_inc(v_x_2527_);
                v___x_2531_ = l_Lean_Syntax_isOfKind(v_x_2527_, v___x_2530_);
                if v___x_2531_ == 0 {
                    leanh::lean_dec(v_x_2527_);
                    v___x_2532_ = leanh::lean_box(1);
                    v___x_2533_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2533_, 0, v___x_2532_);
                    leanh::lean_ctor_set(v___x_2533_, 1, v_a_2529_);
                    return v___x_2533_;
                } else {
                    v___x_2534_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2535_ = l_Lean_Syntax_getArg(v_x_2527_, v___x_2534_);
                    leanh::lean_dec(v_x_2527_);
                    v___x_2536_ = l_Lean_evalPrec(v___x_2535_, v_a_2528_, v_a_2529_);
                    if leanh::lean_obj_tag(v___x_2536_) == 0 {
                        v_a_2537_ = leanh::lean_ctor_get(v___x_2536_, 0);
                        v_a_2538_ = leanh::lean_ctor_get(v___x_2536_, 1);
                        v_isSharedCheck_2548_ =
                            (!leanh::lean_is_exclusive(v___x_2536_)) as u8;
                        if v_isSharedCheck_2548_ == 0 {
                            v___x_2540_ = v___x_2536_;
                            v_isShared_2541_ = v_isSharedCheck_2548_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2538_);
                            leanh::lean_inc(v_a_2537_);
                            leanh::lean_dec(v___x_2536_);
                            v___x_2540_ = leanh::lean_box(0);
                            v_isShared_2541_ = v_isSharedCheck_2548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2549_ = leanh::lean_ctor_get(v___x_2536_, 0);
                        v_a_2550_ = leanh::lean_ctor_get(v___x_2536_, 1);
                        v_isSharedCheck_2557_ =
                            (!leanh::lean_is_exclusive(v___x_2536_)) as u8;
                        if v_isSharedCheck_2557_ == 0 {
                            v___x_2552_ = v___x_2536_;
                            v_isShared_2553_ = v_isSharedCheck_2557_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2550_);
                            leanh::lean_inc(v_a_2549_);
                            leanh::lean_dec(v___x_2536_);
                            v___x_2552_ = leanh::lean_box(0);
                            v_isShared_2553_ = v_isSharedCheck_2557_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2542_ = l_Nat_reprFast(v_a_2537_);
                v___x_2543_ = leanh::lean_box(2);
                v___x_2544_ = l_Lean_Syntax_mkNumLit(v___x_2542_, v___x_2543_);
                if v_isShared_2541_ == 0 {
                    leanh::lean_ctor_set(v___x_2540_, 0, v___x_2544_);
                    v___x_2546_ = v___x_2540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_a_2538_);
                    v___x_2546_ = v_reuseFailAlloc_2547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2546_;
            }
            3 => {
                if v_isShared_2553_ == 0 {
                    v___x_2555_ = v___x_2552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1___boxed(
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_a_2559_: *mut leanh::LeanObject,
    mut v_a_2560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prec____1(
        v_x_2558_, v_a_2559_, v_a_2560_,
    );
    leanh::lean_dec_ref(v_a_2559_);
    return v_res_2561_;
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(
    mut v_x_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2595_: u8 = 0;
    let mut v_a_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut v_a_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2571_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___closed__1;
                leanh::lean_inc(v_x_2568_);
                v___x_2572_ = l_Lean_Syntax_isOfKind(v_x_2568_, v___x_2571_);
                if v___x_2572_ == 0 {
                    leanh::lean_dec(v_x_2568_);
                    v___x_2573_ = leanh::lean_box(1);
                    v___x_2574_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                    leanh::lean_ctor_set(v___x_2574_, 1, v_a_2570_);
                    return v___x_2574_;
                } else {
                    v___x_2575_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2576_ = l_Lean_Syntax_getArg(v_x_2568_, v___x_2575_);
                    v___x_2577_ = l_Lean_evalPrio(v___x_2576_, v_a_2569_, v_a_2570_);
                    if leanh::lean_obj_tag(v___x_2577_) == 0 {
                        v_a_2578_ = leanh::lean_ctor_get(v___x_2577_, 0);
                        leanh::lean_inc(v_a_2578_);
                        v_a_2579_ = leanh::lean_ctor_get(v___x_2577_, 1);
                        leanh::lean_inc(v_a_2579_);
                        leanh::lean_dec_ref_known(v___x_2577_, 2);
                        v___x_2580_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2581_ = l_Lean_Syntax_getArg(v_x_2568_, v___x_2580_);
                        leanh::lean_dec(v_x_2568_);
                        v___x_2582_ = l_Lean_evalPrio(v___x_2581_, v_a_2569_, v_a_2579_);
                        if leanh::lean_obj_tag(v___x_2582_) == 0 {
                            v_a_2583_ = leanh::lean_ctor_get(v___x_2582_, 0);
                            v_a_2584_ = leanh::lean_ctor_get(v___x_2582_, 1);
                            v_isSharedCheck_2595_ =
                                (!leanh::lean_is_exclusive(v___x_2582_)) as u8;
                            if v_isSharedCheck_2595_ == 0 {
                                v___x_2586_ = v___x_2582_;
                                v_isShared_2587_ = v_isSharedCheck_2595_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2584_);
                                leanh::lean_inc(v_a_2583_);
                                leanh::lean_dec(v___x_2582_);
                                v___x_2586_ = leanh::lean_box(0);
                                v_isShared_2587_ = v_isSharedCheck_2595_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2578_);
                            v_a_2596_ = leanh::lean_ctor_get(v___x_2582_, 0);
                            v_a_2597_ = leanh::lean_ctor_get(v___x_2582_, 1);
                            v_isSharedCheck_2604_ =
                                (!leanh::lean_is_exclusive(v___x_2582_)) as u8;
                            if v_isSharedCheck_2604_ == 0 {
                                v___x_2599_ = v___x_2582_;
                                v_isShared_2600_ = v_isSharedCheck_2604_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2597_);
                                leanh::lean_inc(v_a_2596_);
                                leanh::lean_dec(v___x_2582_);
                                v___x_2599_ = leanh::lean_box(0);
                                v_isShared_2600_ = v_isSharedCheck_2604_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_2568_);
                        v_a_2605_ = leanh::lean_ctor_get(v___x_2577_, 0);
                        v_a_2606_ = leanh::lean_ctor_get(v___x_2577_, 1);
                        v_isSharedCheck_2613_ =
                            (!leanh::lean_is_exclusive(v___x_2577_)) as u8;
                        if v_isSharedCheck_2613_ == 0 {
                            v___x_2608_ = v___x_2577_;
                            v_isShared_2609_ = v_isSharedCheck_2613_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2606_);
                            leanh::lean_inc(v_a_2605_);
                            leanh::lean_dec(v___x_2577_);
                            v___x_2608_ = leanh::lean_box(0);
                            v_isShared_2609_ = v_isSharedCheck_2613_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2588_ = lean_nat_add(v_a_2578_, v_a_2583_);
                leanh::lean_dec(v_a_2583_);
                leanh::lean_dec(v_a_2578_);
                v___x_2589_ = l_Nat_reprFast(v___x_2588_);
                v___x_2590_ = leanh::lean_box(2);
                v___x_2591_ = l_Lean_Syntax_mkNumLit(v___x_2589_, v___x_2590_);
                if v_isShared_2587_ == 0 {
                    leanh::lean_ctor_set(v___x_2586_, 0, v___x_2591_);
                    v___x_2593_ = v___x_2586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_a_2584_);
                    v___x_2593_ = v_reuseFailAlloc_2594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2593_;
            }
            3 => {
                if v_isShared_2600_ == 0 {
                    v___x_2602_ = v___x_2599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2596_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_a_2597_);
                    v___x_2602_ = v_reuseFailAlloc_2603_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2602_;
            }
            5 => {
                if v_isShared_2609_ == 0 {
                    v___x_2611_ = v___x_2608_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2612_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_a_2606_);
                    v___x_2611_ = v_reuseFailAlloc_2612_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1___boxed(
    mut v_x_2614_: *mut leanh::LeanObject,
    mut v_a_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrio__1(
        v_x_2614_, v_a_2615_, v_a_2616_,
    );
    leanh::lean_dec_ref(v_a_2615_);
    return v_res_2617_;
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(
    mut v_x_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
    mut v_a_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut v_a_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2656_: u8 = 0;
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_a_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2627_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___closed__1;
                leanh::lean_inc(v_x_2624_);
                v___x_2628_ = l_Lean_Syntax_isOfKind(v_x_2624_, v___x_2627_);
                if v___x_2628_ == 0 {
                    leanh::lean_dec(v_x_2624_);
                    v___x_2629_ = leanh::lean_box(1);
                    v___x_2630_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2630_, 0, v___x_2629_);
                    leanh::lean_ctor_set(v___x_2630_, 1, v_a_2626_);
                    return v___x_2630_;
                } else {
                    v___x_2631_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2632_ = l_Lean_Syntax_getArg(v_x_2624_, v___x_2631_);
                    v___x_2633_ = l_Lean_evalPrio(v___x_2632_, v_a_2625_, v_a_2626_);
                    if leanh::lean_obj_tag(v___x_2633_) == 0 {
                        v_a_2634_ = leanh::lean_ctor_get(v___x_2633_, 0);
                        leanh::lean_inc(v_a_2634_);
                        v_a_2635_ = leanh::lean_ctor_get(v___x_2633_, 1);
                        leanh::lean_inc(v_a_2635_);
                        leanh::lean_dec_ref_known(v___x_2633_, 2);
                        v___x_2636_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2637_ = l_Lean_Syntax_getArg(v_x_2624_, v___x_2636_);
                        leanh::lean_dec(v_x_2624_);
                        v___x_2638_ = l_Lean_evalPrio(v___x_2637_, v_a_2625_, v_a_2635_);
                        if leanh::lean_obj_tag(v___x_2638_) == 0 {
                            v_a_2639_ = leanh::lean_ctor_get(v___x_2638_, 0);
                            v_a_2640_ = leanh::lean_ctor_get(v___x_2638_, 1);
                            v_isSharedCheck_2651_ =
                                (!leanh::lean_is_exclusive(v___x_2638_)) as u8;
                            if v_isSharedCheck_2651_ == 0 {
                                v___x_2642_ = v___x_2638_;
                                v_isShared_2643_ = v_isSharedCheck_2651_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2640_);
                                leanh::lean_inc(v_a_2639_);
                                leanh::lean_dec(v___x_2638_);
                                v___x_2642_ = leanh::lean_box(0);
                                v_isShared_2643_ = v_isSharedCheck_2651_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2634_);
                            v_a_2652_ = leanh::lean_ctor_get(v___x_2638_, 0);
                            v_a_2653_ = leanh::lean_ctor_get(v___x_2638_, 1);
                            v_isSharedCheck_2660_ =
                                (!leanh::lean_is_exclusive(v___x_2638_)) as u8;
                            if v_isSharedCheck_2660_ == 0 {
                                v___x_2655_ = v___x_2638_;
                                v_isShared_2656_ = v_isSharedCheck_2660_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2653_);
                                leanh::lean_inc(v_a_2652_);
                                leanh::lean_dec(v___x_2638_);
                                v___x_2655_ = leanh::lean_box(0);
                                v_isShared_2656_ = v_isSharedCheck_2660_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_2624_);
                        v_a_2661_ = leanh::lean_ctor_get(v___x_2633_, 0);
                        v_a_2662_ = leanh::lean_ctor_get(v___x_2633_, 1);
                        v_isSharedCheck_2669_ =
                            (!leanh::lean_is_exclusive(v___x_2633_)) as u8;
                        if v_isSharedCheck_2669_ == 0 {
                            v___x_2664_ = v___x_2633_;
                            v_isShared_2665_ = v_isSharedCheck_2669_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2662_);
                            leanh::lean_inc(v_a_2661_);
                            leanh::lean_dec(v___x_2633_);
                            v___x_2664_ = leanh::lean_box(0);
                            v_isShared_2665_ = v_isSharedCheck_2669_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2644_ = lean_nat_sub(v_a_2634_, v_a_2639_);
                leanh::lean_dec(v_a_2639_);
                leanh::lean_dec(v_a_2634_);
                v___x_2645_ = l_Nat_reprFast(v___x_2644_);
                v___x_2646_ = leanh::lean_box(2);
                v___x_2647_ = l_Lean_Syntax_mkNumLit(v___x_2645_, v___x_2646_);
                if v_isShared_2643_ == 0 {
                    leanh::lean_ctor_set(v___x_2642_, 0, v___x_2647_);
                    v___x_2649_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_a_2640_);
                    v___x_2649_ = v_reuseFailAlloc_2650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2649_;
            }
            3 => {
                if v_isShared_2656_ == 0 {
                    v___x_2658_ = v___x_2655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2659_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_a_2653_);
                    v___x_2658_ = v_reuseFailAlloc_2659_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2658_;
            }
            5 => {
                if v_isShared_2665_ == 0 {
                    v___x_2667_ = v___x_2664_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_a_2662_);
                    v___x_2667_ = v_reuseFailAlloc_2668_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1___boxed(
    mut v_x_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__subPrio__1(
        v_x_2670_, v_a_2671_, v_a_2672_,
    );
    leanh::lean_dec_ref(v_a_2671_);
    return v_res_2673_;
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(
    mut v_x_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2710_: u8 = 0;
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut v_a_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2699_ = l_Lean_termEval__prio___00__closed__1;
                leanh::lean_inc(v_x_2696_);
                v___x_2700_ = l_Lean_Syntax_isOfKind(v_x_2696_, v___x_2699_);
                if v___x_2700_ == 0 {
                    leanh::lean_dec(v_x_2696_);
                    v___x_2701_ = leanh::lean_box(1);
                    v___x_2702_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                    leanh::lean_ctor_set(v___x_2702_, 1, v_a_2698_);
                    return v___x_2702_;
                } else {
                    v___x_2703_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2704_ = l_Lean_Syntax_getArg(v_x_2696_, v___x_2703_);
                    leanh::lean_dec(v_x_2696_);
                    v___x_2705_ = l_Lean_evalPrio(v___x_2704_, v_a_2697_, v_a_2698_);
                    if leanh::lean_obj_tag(v___x_2705_) == 0 {
                        v_a_2706_ = leanh::lean_ctor_get(v___x_2705_, 0);
                        v_a_2707_ = leanh::lean_ctor_get(v___x_2705_, 1);
                        v_isSharedCheck_2717_ =
                            (!leanh::lean_is_exclusive(v___x_2705_)) as u8;
                        if v_isSharedCheck_2717_ == 0 {
                            v___x_2709_ = v___x_2705_;
                            v_isShared_2710_ = v_isSharedCheck_2717_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2707_);
                            leanh::lean_inc(v_a_2706_);
                            leanh::lean_dec(v___x_2705_);
                            v___x_2709_ = leanh::lean_box(0);
                            v_isShared_2710_ = v_isSharedCheck_2717_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2718_ = leanh::lean_ctor_get(v___x_2705_, 0);
                        v_a_2719_ = leanh::lean_ctor_get(v___x_2705_, 1);
                        v_isSharedCheck_2726_ =
                            (!leanh::lean_is_exclusive(v___x_2705_)) as u8;
                        if v_isSharedCheck_2726_ == 0 {
                            v___x_2721_ = v___x_2705_;
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2719_);
                            leanh::lean_inc(v_a_2718_);
                            leanh::lean_dec(v___x_2705_);
                            v___x_2721_ = leanh::lean_box(0);
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2711_ = l_Nat_reprFast(v_a_2706_);
                v___x_2712_ = leanh::lean_box(2);
                v___x_2713_ = l_Lean_Syntax_mkNumLit(v___x_2711_, v___x_2712_);
                if v_isShared_2710_ == 0 {
                    leanh::lean_ctor_set(v___x_2709_, 0, v___x_2713_);
                    v___x_2715_ = v___x_2709_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_a_2707_);
                    v___x_2715_ = v_reuseFailAlloc_2716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2715_;
            }
            3 => {
                if v_isShared_2722_ == 0 {
                    v___x_2724_ = v___x_2721_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_a_2719_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1___boxed(
    mut v_x_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l_Lean___aux__Init__Meta______macroRules__Lean__termEval__prio____1(
        v_x_2727_, v_a_2728_, v_a_2729_,
    );
    leanh::lean_dec_ref(v_a_2728_);
    return v_res_2730_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l_Lean_Parser_Tactic_optConfig;
    v___x_2743_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__4;
    v___x_2744_ = l_Lean_termEval__prec___00__closed__3;
    v___x_2745_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2744_);
    leanh::lean_ctor_set(v___x_2745_, 1, v___x_2743_);
    leanh::lean_ctor_set(v___x_2745_, 2, v___x_2742_);
    return v___x_2745_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_2747_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__5_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__5,
    );
    v___x_2748_ = l_Lean_termEval__prec___00__closed__3;
    v___x_2749_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
    leanh::lean_ctor_set(v___x_2749_, 1, v___x_2747_);
    leanh::lean_ctor_set(v___x_2749_, 2, v___x_2746_);
    return v___x_2749_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ = l_Lean_Parser_Tactic_location;
    v___x_2754_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__8;
    v___x_2755_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2755_, 0, v___x_2754_);
    leanh::lean_ctor_set(v___x_2755_, 1, v___x_2753_);
    return v___x_2755_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9,
    );
    v___x_2757_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__6_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__6,
    );
    v___x_2758_ = l_Lean_termEval__prec___00__closed__3;
    v___x_2759_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2759_, 0, v___x_2758_);
    leanh::lean_ctor_set(v___x_2759_, 1, v___x_2757_);
    leanh::lean_ctor_set(v___x_2759_, 2, v___x_2756_);
    return v___x_2759_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2760_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__10_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__10,
    );
    v___x_2761_ = leanh::lean_unsigned_to_nat(1022);
    v___x_2762_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__2;
    v___x_2763_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2763_, 0, v___x_2762_);
    leanh::lean_ctor_set(v___x_2763_, 1, v___x_2761_);
    leanh::lean_ctor_set(v___x_2763_, 2, v___x_2760_);
    return v___x_2763_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_tacticErw______() -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__11_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__11,
    );
    return v___x_2764_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(
    mut v_sz_2765_: usize,
    mut v_i_2766_: usize,
    mut v_bs_2767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2768_: u8 = 0;
    let mut v_v_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: usize = 0;
    let mut v___x_2773_: usize = 0;
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2768_ = lean_usize_dec_lt(v_i_2766_, v_sz_2765_);
                if v___x_2768_ == 0 {
                    return v_bs_2767_;
                } else {
                    v_v_2769_ = lean_array_uget(v_bs_2767_, v_i_2766_);
                    v___x_2770_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2771_ = lean_array_uset(v_bs_2767_, v_i_2766_, v___x_2770_);
                    v___x_2772_ = 1usize;
                    v___x_2773_ = lean_usize_add(v_i_2766_, v___x_2772_);
                    v___x_2774_ = lean_array_uset(v_bs_x27_2771_, v_i_2766_, v_v_2769_);
                    v_i_2766_ = v___x_2773_;
                    v_bs_2767_ = v___x_2774_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0___boxed(
    mut v_sz_2776_: *mut leanh::LeanObject,
    mut v_i_2777_: *mut leanh::LeanObject,
    mut v_bs_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2779_: usize = 0;
    let mut v_i_boxed_2780_: usize = 0;
    let mut v_res_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2779_ = leanh::lean_unbox_usize(v_sz_2776_);
    leanh::lean_dec(v_sz_2776_);
    v_i_boxed_2780_ = leanh::lean_unbox_usize(v_i_2777_);
    leanh::lean_dec(v_i_2777_);
    v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_boxed_2779_, v_i_boxed_2780_, v_bs_2778_);
    return v_res_2781_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2798_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2813_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__13;
    v___x_2814_ = l_String_toRawSubstring_x27(v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__21;
    v___x_2828_ = l_String_toRawSubstring_x27(v___x_2827_);
    return v___x_2828_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(
    mut v_x_2849_: *mut leanh::LeanObject,
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2886_: usize = 0;
    let mut v___x_2887_: usize = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2852_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__2;
                leanh::lean_inc(v_x_2849_);
                v___x_2853_ = l_Lean_Syntax_isOfKind(v_x_2849_, v___x_2852_);
                if v___x_2853_ == 0 {
                    leanh::lean_dec(v_x_2849_);
                    v___x_2854_ = leanh::lean_box(1);
                    v___x_2855_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2855_, 0, v___x_2854_);
                    leanh::lean_ctor_set(v___x_2855_, 1, v_a_2851_);
                    return v___x_2855_;
                } else {
                    v___x_2856_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2857_ = l_Lean_Syntax_getArg(v_x_2849_, v___x_2856_);
                    v___x_2858_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2859_ = l_Lean_Syntax_getArg(v_x_2849_, v___x_2858_);
                    v___x_2921_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2922_ = l_Lean_Syntax_getArg(v_x_2849_, v___x_2921_);
                    leanh::lean_dec(v_x_2849_);
                    v___x_2923_ = l_Lean_Syntax_getOptional_x3f(v___x_2922_);
                    leanh::lean_dec(v___x_2922_);
                    if leanh::lean_obj_tag(v___x_2923_) == 0 {
                        v___x_2924_ = leanh::lean_box(0);
                        v___y_2873_ = v___x_2924_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2925_ = leanh::lean_ctor_get(v___x_2923_, 0);
                        v_isSharedCheck_2932_ =
                            (!leanh::lean_is_exclusive(v___x_2923_)) as u8;
                        if v_isSharedCheck_2932_ == 0 {
                            v___x_2927_ = v___x_2923_;
                            v_isShared_2928_ = v_isSharedCheck_2932_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2925_);
                            leanh::lean_dec(v___x_2923_);
                            v___x_2927_ = leanh::lean_box(0);
                            v_isShared_2928_ = v_isSharedCheck_2932_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2868_ = l_Array_append___redArg(v___y_2863_, v___y_2867_);
                leanh::lean_dec_ref(v___y_2867_);
                leanh::lean_inc(v___y_2866_);
                leanh::lean_inc(v___y_2861_);
                v___x_2869_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2869_, 0, v___y_2861_);
                leanh::lean_ctor_set(v___x_2869_, 1, v___y_2866_);
                leanh::lean_ctor_set(v___x_2869_, 2, v___x_2868_);
                leanh::lean_inc(v___y_2865_);
                v___x_2870_ = l_Lean_Syntax_node4(
                    v___y_2861_,
                    v___y_2865_,
                    v___y_2864_,
                    v___y_2862_,
                    v___x_2859_,
                    v___x_2869_,
                );
                v___x_2871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2871_, 0, v___x_2870_);
                leanh::lean_ctor_set(v___x_2871_, 1, v_a_2851_);
                return v___x_2871_;
            }
            2 => {
                v_quotContext_2874_ = leanh::lean_ctor_get(v_a_2850_, 1);
                v_currMacroScope_2875_ = leanh::lean_ctor_get(v_a_2850_, 2);
                v_ref_2876_ = leanh::lean_ctor_get(v_a_2850_, 5);
                v___x_2877_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1;
                v___x_2878_ = 0;
                v___x_2879_ = l_Lean_SourceInfo_fromRef(v_ref_2876_, v___x_2878_);
                v___x_2880_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__3;
                v___x_2881_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__4;
                leanh::lean_inc_n(v___x_2879_, 12);
                v___x_2882_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2882_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2882_, 1, v___x_2881_);
                v___x_2883_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
                v___x_2884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
                v___x_2885_ = l_Lean_Parser_Tactic_getConfigItems(v___x_2857_);
                v_sz_2886_ = lean_array_size(v___x_2885_);
                v___x_2887_ = 0usize;
                v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(v_sz_2886_, v___x_2887_, v___x_2885_);
                v___x_2889_ = l_Array_append___redArg(v___x_2884_, v___x_2888_);
                leanh::lean_dec_ref(v___x_2888_);
                v___x_2890_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9;
                v___x_2891_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11;
                v___x_2892_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
                v___x_2893_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2893_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2893_, 1, v___x_2892_);
                v___x_2894_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__14);
                v___x_2895_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__15;
                leanh::lean_inc_n(v_currMacroScope_2875_, 2);
                leanh::lean_inc_n(v_quotContext_2874_, 2);
                v___x_2896_ =
                    l_Lean_addMacroScope(v_quotContext_2874_, v___x_2895_, v_currMacroScope_2875_);
                v___x_2897_ = leanh::lean_box(0);
                v___x_2898_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2898_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2898_, 1, v___x_2894_);
                leanh::lean_ctor_set(v___x_2898_, 2, v___x_2896_);
                leanh::lean_ctor_set(v___x_2898_, 3, v___x_2897_);
                v___x_2899_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
                v___x_2900_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2900_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2900_, 1, v___x_2899_);
                v___x_2901_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__19;
                v___x_2902_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__20;
                v___x_2903_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2903_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                v___x_2904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__22);
                v___x_2905_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__23;
                v___x_2906_ =
                    l_Lean_addMacroScope(v_quotContext_2874_, v___x_2905_, v_currMacroScope_2875_);
                v___x_2907_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__29;
                v___x_2908_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2908_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2908_, 1, v___x_2904_);
                leanh::lean_ctor_set(v___x_2908_, 2, v___x_2906_);
                leanh::lean_ctor_set(v___x_2908_, 3, v___x_2907_);
                v___x_2909_ =
                    l_Lean_Syntax_node2(v___x_2879_, v___x_2901_, v___x_2903_, v___x_2908_);
                v___x_2910_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
                v___x_2911_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2911_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2911_, 1, v___x_2910_);
                v___x_2912_ = l_Lean_Syntax_node5(
                    v___x_2879_,
                    v___x_2891_,
                    v___x_2893_,
                    v___x_2898_,
                    v___x_2900_,
                    v___x_2909_,
                    v___x_2911_,
                );
                v___x_2913_ = l_Lean_Syntax_node1(v___x_2879_, v___x_2890_, v___x_2912_);
                v___x_2914_ = lean_array_push(v___x_2889_, v___x_2913_);
                v___x_2915_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2915_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2915_, 1, v___x_2883_);
                leanh::lean_ctor_set(v___x_2915_, 2, v___x_2914_);
                v___x_2916_ = l_Lean_Syntax_node1(v___x_2879_, v___x_2877_, v___x_2915_);
                if leanh::lean_obj_tag(v___y_2873_) == 0 {
                    v___x_2917_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31;
                    v___y_2861_ = v___x_2879_;
                    v___y_2862_ = v___x_2916_;
                    v___y_2863_ = v___x_2884_;
                    v___y_2864_ = v___x_2882_;
                    v___y_2865_ = v___x_2880_;
                    v___y_2866_ = v___x_2883_;
                    v___y_2867_ = v___x_2917_;
                    state = 1;
                    continue;
                } else {
                    v_val_2918_ = leanh::lean_ctor_get(v___y_2873_, 0);
                    leanh::lean_inc(v_val_2918_);
                    leanh::lean_dec_ref_known(v___y_2873_, 1);
                    v___x_2919_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31;
                    v___x_2920_ = lean_array_push(v___x_2919_, v_val_2918_);
                    v___y_2861_ = v___x_2879_;
                    v___y_2862_ = v___x_2916_;
                    v___y_2863_ = v___x_2884_;
                    v___y_2864_ = v___x_2882_;
                    v___y_2865_ = v___x_2880_;
                    v___y_2866_ = v___x_2883_;
                    v___y_2867_ = v___x_2920_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2928_ == 0 {
                    v___x_2930_ = v___x_2927_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_val_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2873_ = v___x_2930_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___boxed(
    mut v_x_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
    mut v_a_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1(v_x_2933_, v_a_2934_, v_a_2935_);
    leanh::lean_dec_ref(v_a_2934_);
    return v_res_2936_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3097_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__30;
    v___x_3098_ = l_Lean_termEval__prec___00__closed__3;
    v___x_3099_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3099_, 0, v___x_3098_);
    leanh::lean_ctor_set(v___x_3099_, 1, v___x_3097_);
    leanh::lean_ctor_set(v___x_3099_, 2, v___x_3096_);
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31_once),
        _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__31,
    );
    v___x_3101_ = leanh::lean_unsigned_to_nat(1022);
    v___x_3102_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1;
    v___x_3103_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3103_, 0, v___x_3102_);
    leanh::lean_ctor_set(v___x_3103_, 1, v___x_3101_);
    leanh::lean_ctor_set(v___x_3103_, 2, v___x_3100_);
    return v___x_3103_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_declareSimpLikeTactic() -> *mut leanh::LeanObject {
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32_once),
        _init_l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__32,
    );
    return v___x_3104_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(
    mut v_____do__lift_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = 0;
    v___x_3109_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3105_, v___x_3108_);
    v___x_3110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
    leanh::lean_ctor_set(v___x_3110_, 1, v___y_3107_);
    return v___x_3110_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0___boxed(
    mut v_____do__lift_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_____do__lift_3111_, v___y_3112_, v___y_3113_);
    leanh::lean_dec_ref(v___y_3112_);
    leanh::lean_dec(v_____do__lift_3111_);
    return v_res_3114_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__14;
    v___x_3131_ = l_String_toRawSubstring_x27(v___x_3130_);
    return v___x_3131_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20;
    v___x_3139_ = l_String_toRawSubstring_x27(v___x_3138_);
    return v___x_3139_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3146_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__26;
    v___x_3147_ = l_String_toRawSubstring_x27(v___x_3146_);
    return v___x_3147_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__37;
    v___x_3160_ = l_String_toRawSubstring_x27(v___x_3159_);
    return v___x_3160_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__50;
    v___x_3175_ = l_String_toRawSubstring_x27(v___x_3174_);
    return v___x_3175_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55()
-> *mut leanh::LeanObject {
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__54;
    v___x_3182_ = l_String_toRawSubstring_x27(v___x_3181_);
    return v___x_3182_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__65;
    v___x_3198_ = l_String_toRawSubstring_x27(v___x_3197_);
    return v___x_3198_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68()
-> *mut leanh::LeanObject {
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3200_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67;
    v___x_3201_ = l_String_toRawSubstring_x27(v___x_3200_);
    return v___x_3201_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75()
-> *mut leanh::LeanObject {
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__74;
    v___x_3211_ = l_String_toRawSubstring_x27(v___x_3210_);
    return v___x_3211_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77()
-> *mut leanh::LeanObject {
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3214_ = l_Lean_Parser_Tactic_simpAllKind___closed__13;
    v___x_3215_ = l_String_toRawSubstring_x27(v___x_3214_);
    return v___x_3215_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85()
-> *mut leanh::LeanObject {
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84;
    v___x_3231_ = l_String_toRawSubstring_x27(v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88()
-> *mut leanh::LeanObject {
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3235_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__87;
    v___x_3236_ = l_String_toRawSubstring_x27(v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(
    mut v___x_3245_: *mut leanh::LeanObject,
    mut v___x_3246_: *mut leanh::LeanObject,
    mut v___x_3247_: *mut leanh::LeanObject,
    mut v___x_3248_: *mut leanh::LeanObject,
    mut v___x_3249_: *mut leanh::LeanObject,
    mut v___x_3250_: *mut leanh::LeanObject,
    mut v___x_3251_: *mut leanh::LeanObject,
    mut v___x_3252_: *mut leanh::LeanObject,
    mut v_____x_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_fst_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v_quotContext_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3256_ = leanh::lean_ctor_get(v_____x_3253_, 1);
                v_fst_3257_ = leanh::lean_ctor_get(v_____x_3253_, 0);
                v_isSharedCheck_3527_ = (!leanh::lean_is_exclusive(v_____x_3253_)) as u8;
                if v_isSharedCheck_3527_ == 0 {
                    v___x_3259_ = v_____x_3253_;
                    v_isShared_3260_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3256_);
                    leanh::lean_inc(v_fst_3257_);
                    leanh::lean_dec(v_____x_3253_);
                    v___x_3259_ = leanh::lean_box(0);
                    v_isShared_3260_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3261_ = leanh::lean_ctor_get(v_snd_3256_, 0);
                v_snd_3262_ = leanh::lean_ctor_get(v_snd_3256_, 1);
                v_isSharedCheck_3526_ = (!leanh::lean_is_exclusive(v_snd_3256_)) as u8;
                if v_isSharedCheck_3526_ == 0 {
                    v___x_3264_ = v_snd_3256_;
                    v_isShared_3265_ = v_isSharedCheck_3526_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3262_);
                    leanh::lean_inc(v_fst_3261_);
                    leanh::lean_dec(v_snd_3256_);
                    v___x_3264_ = leanh::lean_box(0);
                    v_isShared_3265_ = v_isSharedCheck_3526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_quotContext_3266_ = leanh::lean_ctor_get(v___y_3254_, 1);
                v_currMacroScope_3267_ = leanh::lean_ctor_get(v___y_3254_, 2);
                v_ref_3268_ = leanh::lean_ctor_get(v___y_3254_, 5);
                v___x_3269_ = 0;
                v___x_3270_ = l_Lean_SourceInfo_fromRef(v_ref_3268_, v___x_3269_);
                v___x_3271_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
                v___x_3272_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0;
                v___x_3273_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__1;
                leanh::lean_inc_ref_n(v___x_3246_, 3);
                leanh::lean_inc_ref_n(v___x_3245_, 3);
                v___x_3274_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3273_);
                v___x_3275_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__2;
                v___x_3276_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3275_);
                v___x_3277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
                leanh::lean_inc_n(v___x_3270_, 2);
                v___x_3278_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3278_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3278_, 1, v___x_3271_);
                leanh::lean_ctor_set(v___x_3278_, 2, v___x_3277_);
                v___x_3279_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17;
                v___x_3280_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__3;
                v___x_3281_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3280_);
                v___x_3282_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__4;
                if v_isShared_3265_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3264_, 2);
                    leanh::lean_ctor_set(v___x_3264_, 1, v___x_3282_);
                    leanh::lean_ctor_set(v___x_3264_, 0, v___x_3270_);
                    v___x_3284_ = v___x_3264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3525_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3285_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__5;
                leanh::lean_inc_ref_n(v___x_3246_, 3);
                leanh::lean_inc_ref_n(v___x_3245_, 3);
                v___x_3286_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3285_);
                v___x_3287_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6;
                v___x_3288_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3287_);
                leanh::lean_inc_ref(v___x_3278_);
                leanh::lean_inc_n(v___x_3270_, 2);
                v___x_3289_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3288_, v___x_3278_);
                v___x_3290_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__7;
                v___x_3291_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__8;
                v___x_3292_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3290_, v___x_3291_);
                if v_isShared_3260_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3259_, 2);
                    leanh::lean_ctor_set(v___x_3259_, 1, v___x_3291_);
                    leanh::lean_ctor_set(v___x_3259_, 0, v___x_3270_);
                    v___x_3294_ = v___x_3259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3291_);
                    v___x_3294_ = v_reuseFailAlloc_3524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_n(v___x_3270_, 97);
                v___x_3295_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3292_, v___x_3294_, v___x_3247_);
                v___x_3296_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3286_, v___x_3289_, v___x_3295_);
                v___x_3297_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3296_);
                v___x_3298_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__9;
                v___x_3299_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3299_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3299_, 1, v___x_3298_);
                leanh::lean_inc_ref_n(v___x_3299_, 2);
                v___x_3300_ = l_Lean_Syntax_node3(
                    v___x_3270_,
                    v___x_3281_,
                    v___x_3284_,
                    v___x_3297_,
                    v___x_3299_,
                );
                v___x_3301_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3300_);
                v___x_3302_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__10;
                leanh::lean_inc_ref_n(v___x_3246_, 27);
                leanh::lean_inc_ref_n(v___x_3245_, 29);
                v___x_3303_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3302_);
                v___x_3304_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3304_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3304_, 1, v___x_3302_);
                v___x_3305_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3303_, v___x_3304_);
                v___x_3306_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3305_);
                leanh::lean_inc_ref_n(v___x_3278_, 32);
                v___x_3307_ = l_Lean_Syntax_node7(
                    v___x_3270_,
                    v___x_3276_,
                    v___x_3278_,
                    v___x_3301_,
                    v___x_3278_,
                    v___x_3278_,
                    v___x_3306_,
                    v___x_3278_,
                    v___x_3278_,
                );
                v___x_3308_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__11;
                v___x_3309_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3308_);
                v___x_3310_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__12;
                v___x_3311_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3311_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3311_, 1, v___x_3310_);
                v___x_3312_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__13;
                v___x_3313_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3312_);
                v___x_3314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__15);
                v___x_3315_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__16;
                leanh::lean_inc_n(v_currMacroScope_3267_, 13);
                leanh::lean_inc_n(v_quotContext_3266_, 13);
                v___x_3316_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3315_, v_currMacroScope_3267_);
                v___x_3317_ = leanh::lean_box(0);
                v___x_3318_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3318_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3318_, 1, v___x_3314_);
                leanh::lean_ctor_set(v___x_3318_, 2, v___x_3316_);
                leanh::lean_ctor_set(v___x_3318_, 3, v___x_3317_);
                v___x_3319_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3313_, v___x_3318_, v___x_3278_);
                v___x_3320_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__17;
                v___x_3321_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3320_);
                v___x_3322_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__18;
                v___x_3323_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3322_);
                v___x_3324_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19;
                v___x_3325_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3325_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3325_, 1, v___x_3324_);
                v___x_3326_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__20;
                v___x_3327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__21);
                v___x_3328_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__22;
                v___x_3329_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3328_, v_currMacroScope_3267_);
                v___x_3330_ = l_Lean_Name_mkStr2(v___x_3245_, v___x_3326_);
                leanh::lean_inc(v___x_3330_);
                v___x_3331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3331_, 0, v___x_3330_);
                leanh::lean_ctor_set(v___x_3331_, 1, v___x_3317_);
                v___x_3332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3332_, 0, v___x_3330_);
                v___x_3333_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3333_, 0, v___x_3332_);
                leanh::lean_ctor_set(v___x_3333_, 1, v___x_3317_);
                v___x_3334_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3334_, 0, v___x_3331_);
                leanh::lean_ctor_set(v___x_3334_, 1, v___x_3333_);
                v___x_3335_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3335_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3335_, 1, v___x_3327_);
                leanh::lean_ctor_set(v___x_3335_, 2, v___x_3329_);
                leanh::lean_ctor_set(v___x_3335_, 3, v___x_3334_);
                v___x_3336_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3323_, v___x_3325_, v___x_3335_);
                v___x_3337_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3336_);
                v___x_3338_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3321_, v___x_3278_, v___x_3337_);
                v___x_3339_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__23;
                v___x_3340_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3272_, v___x_3339_);
                v___x_3341_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
                v___x_3342_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3342_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3342_, 1, v___x_3341_);
                v___x_3343_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__24;
                v___x_3344_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3343_);
                v___x_3345_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3345_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3345_, 1, v___x_3343_);
                v___x_3346_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__25;
                v___x_3347_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3346_);
                v___x_3348_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__27);
                v___x_3349_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__28;
                v___x_3350_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3349_, v_currMacroScope_3267_);
                v___x_3351_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3351_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3351_, 1, v___x_3348_);
                leanh::lean_ctor_set(v___x_3351_, 2, v___x_3350_);
                leanh::lean_ctor_set(v___x_3351_, 3, v___x_3317_);
                leanh::lean_inc_ref_n(v___x_3351_, 3);
                v___x_3352_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3351_);
                v___x_3353_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__29;
                v___x_3354_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3354_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                v___x_3355_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__30;
                v___x_3356_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3355_);
                v___x_3357_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3357_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3357_, 1, v___x_3355_);
                v___x_3358_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__31;
                v___x_3359_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3358_);
                v___x_3360_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__32;
                v___x_3361_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3360_);
                v___x_3362_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__33;
                v___x_3363_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3362_);
                v___x_3364_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__34;
                v___x_3365_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3365_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                v___x_3366_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__35;
                v___x_3367_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3366_);
                v___x_3368_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3367_, v___x_3278_);
                v___x_3369_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__36;
                v___x_3370_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3369_);
                v___x_3371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__38);
                v___x_3372_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__39;
                v___x_3373_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3372_, v_currMacroScope_3267_);
                v___x_3374_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3374_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3374_, 1, v___x_3371_);
                leanh::lean_ctor_set(v___x_3374_, 2, v___x_3373_);
                leanh::lean_ctor_set(v___x_3374_, 3, v___x_3317_);
                v___x_3375_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__40;
                v___x_3376_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3376_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3376_, 1, v___x_3375_);
                v___x_3377_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__41;
                v___x_3378_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3377_);
                v___x_3379_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__42;
                v___x_3380_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3379_);
                v___x_3381_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__43;
                v___x_3382_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3382_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3382_, 1, v___x_3381_);
                leanh::lean_inc_ref(v___x_3248_);
                v___x_3383_ = l_String_toRawSubstring_x27(v___x_3248_);
                v___x_3384_ = l_Lean_Name_mkStr1(v___x_3248_);
                v___x_3385_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3384_, v_currMacroScope_3267_);
                v___x_3386_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3386_, 0, v___x_3249_);
                leanh::lean_ctor_set(v___x_3386_, 1, v___x_3317_);
                v___x_3387_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3387_, 0, v___x_3386_);
                leanh::lean_ctor_set(v___x_3387_, 1, v___x_3317_);
                v___x_3388_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3388_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3388_, 1, v___x_3383_);
                leanh::lean_ctor_set(v___x_3388_, 2, v___x_3385_);
                leanh::lean_ctor_set(v___x_3388_, 3, v___x_3387_);
                v___x_3389_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__44;
                v___x_3390_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3390_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3390_, 1, v___x_3389_);
                v___x_3391_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
                v___x_3392_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3392_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3392_, 1, v___x_3391_);
                leanh::lean_inc_ref_n(v___x_3392_, 3);
                v___x_3393_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3380_,
                    v___x_3382_,
                    v___x_3388_,
                    v___x_3390_,
                    v___x_3250_,
                    v___x_3392_,
                );
                v___x_3394_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3378_, v___x_3393_);
                leanh::lean_inc_ref(v___x_3374_);
                v___x_3395_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3370_,
                    v___x_3374_,
                    v___x_3278_,
                    v___x_3376_,
                    v___x_3394_,
                );
                leanh::lean_inc_n(v___x_3368_, 4);
                leanh::lean_inc_ref_n(v___x_3365_, 4);
                v___x_3396_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3363_,
                    v___x_3365_,
                    v___x_3278_,
                    v___x_3368_,
                    v___x_3395_,
                );
                leanh::lean_inc_n(v___x_3361_, 5);
                v___x_3397_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3396_, v___x_3278_);
                v___x_3398_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__45;
                v___x_3399_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3398_);
                v___x_3400_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__46;
                v___x_3401_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3400_);
                v___x_3402_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__47;
                v___x_3403_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3402_);
                v___x_3404_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__48;
                v___x_3405_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3404_);
                v___x_3406_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3405_, v___x_3351_);
                v___x_3407_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__49;
                v___x_3408_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3407_);
                v___x_3409_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__51);
                v___x_3410_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__53;
                v___x_3411_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3410_, v_currMacroScope_3267_);
                v___x_3412_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3412_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3412_, 1, v___x_3409_);
                leanh::lean_ctor_set(v___x_3412_, 2, v___x_3411_);
                leanh::lean_ctor_set(v___x_3412_, 3, v___x_3317_);
                v___x_3413_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v_fst_3257_);
                leanh::lean_inc_n(v___x_3408_, 4);
                v___x_3414_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3408_, v___x_3412_, v___x_3413_);
                leanh::lean_inc_ref_n(v___x_3342_, 5);
                leanh::lean_inc_n(v___x_3406_, 3);
                leanh::lean_inc_n(v___x_3403_, 3);
                v___x_3415_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3403_,
                    v___x_3406_,
                    v___x_3278_,
                    v___x_3278_,
                    v___x_3342_,
                    v___x_3414_,
                );
                leanh::lean_inc_n(v___x_3401_, 3);
                v___x_3416_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3401_, v___x_3415_);
                leanh::lean_inc_n(v___x_3399_, 3);
                v___x_3417_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3399_,
                    v___x_3365_,
                    v___x_3278_,
                    v___x_3368_,
                    v___x_3416_,
                );
                v___x_3418_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3417_, v___x_3278_);
                v___x_3419_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__55);
                v___x_3420_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__57;
                v___x_3421_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3420_, v_currMacroScope_3267_);
                v___x_3422_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3422_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3422_, 1, v___x_3419_);
                leanh::lean_ctor_set(v___x_3422_, 2, v___x_3421_);
                leanh::lean_ctor_set(v___x_3422_, 3, v___x_3317_);
                v___x_3423_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__59;
                v___x_3424_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__60;
                v___x_3425_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3425_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3425_, 1, v___x_3424_);
                v___x_3426_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3423_, v___x_3425_);
                v___x_3427_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__61;
                v___x_3428_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3427_);
                v___x_3429_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__62;
                v___x_3430_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3429_);
                v___x_3431_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
                v___x_3432_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3432_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3432_, 1, v___x_3431_);
                v___x_3433_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__64;
                v___x_3434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__66);
                v___x_3435_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3251_, v_currMacroScope_3267_);
                leanh::lean_inc_ref(v___x_3252_);
                v___x_3436_ = l_Lean_Name_mkStr3(v___x_3245_, v___x_3246_, v___x_3252_);
                v___x_3437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3437_, 0, v___x_3436_);
                v___x_3438_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3438_, 0, v___x_3437_);
                leanh::lean_ctor_set(v___x_3438_, 1, v___x_3317_);
                v___x_3439_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3439_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3439_, 1, v___x_3434_);
                leanh::lean_ctor_set(v___x_3439_, 2, v___x_3435_);
                leanh::lean_ctor_set(v___x_3439_, 3, v___x_3438_);
                v___x_3440_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3433_, v___x_3439_);
                leanh::lean_inc_ref(v___x_3432_);
                v___x_3441_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3430_, v___x_3432_, v___x_3440_);
                v___x_3442_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__67;
                v___x_3443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__68);
                v___x_3444_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__69;
                v___x_3445_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3444_, v_currMacroScope_3267_);
                v___x_3446_ = l_Lean_Name_mkStr2(v___x_3245_, v___x_3442_);
                v___x_3447_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3447_, 0, v___x_3446_);
                leanh::lean_ctor_set(v___x_3447_, 1, v___x_3317_);
                v___x_3448_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3448_, 0, v___x_3447_);
                leanh::lean_ctor_set(v___x_3448_, 1, v___x_3317_);
                v___x_3449_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3449_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3449_, 1, v___x_3443_);
                leanh::lean_ctor_set(v___x_3449_, 2, v___x_3445_);
                leanh::lean_ctor_set(v___x_3449_, 3, v___x_3448_);
                v___x_3450_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__71;
                v___x_3451_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__72;
                v___x_3452_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3452_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3452_, 1, v___x_3451_);
                leanh::lean_inc(v___x_3426_);
                leanh::lean_inc_ref(v___x_3452_);
                v___x_3453_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3450_,
                    v___x_3351_,
                    v___x_3452_,
                    v___x_3426_,
                    v___x_3299_,
                );
                v___x_3454_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__73;
                v___x_3455_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3454_);
                v___x_3456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__75);
                v___x_3457_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__76;
                v___x_3458_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3457_, v_currMacroScope_3267_);
                v___x_3459_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3459_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3459_, 1, v___x_3456_);
                leanh::lean_ctor_set(v___x_3459_, 2, v___x_3458_);
                leanh::lean_ctor_set(v___x_3459_, 3, v___x_3317_);
                v___x_3460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
                v___x_3461_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78;
                v___x_3462_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3461_, v_currMacroScope_3267_);
                v___x_3463_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82;
                v___x_3464_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3464_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3464_, 1, v___x_3460_);
                leanh::lean_ctor_set(v___x_3464_, 2, v___x_3462_);
                leanh::lean_ctor_set(v___x_3464_, 3, v___x_3463_);
                v___x_3465_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3455_,
                    v___x_3432_,
                    v___x_3459_,
                    v___x_3342_,
                    v___x_3464_,
                    v___x_3392_,
                );
                v___x_3466_ = l_Lean_Syntax_node3(
                    v___x_3270_,
                    v___x_3271_,
                    v___x_3453_,
                    v_fst_3261_,
                    v___x_3465_,
                );
                v___x_3467_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3408_, v___x_3449_, v___x_3466_);
                leanh::lean_inc(v___x_3441_);
                leanh::lean_inc(v___x_3428_);
                v___x_3468_ = l_Lean_Syntax_node3(
                    v___x_3270_,
                    v___x_3428_,
                    v___x_3441_,
                    v___x_3467_,
                    v___x_3392_,
                );
                v___x_3469_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3271_, v___x_3426_, v___x_3468_);
                leanh::lean_inc_ref(v___x_3422_);
                v___x_3470_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3408_, v___x_3422_, v___x_3469_);
                v___x_3471_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3403_,
                    v___x_3406_,
                    v___x_3278_,
                    v___x_3278_,
                    v___x_3342_,
                    v___x_3470_,
                );
                v___x_3472_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3401_, v___x_3471_);
                v___x_3473_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3399_,
                    v___x_3365_,
                    v___x_3278_,
                    v___x_3368_,
                    v___x_3472_,
                );
                v___x_3474_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3473_, v___x_3278_);
                v___x_3475_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__83;
                v___x_3476_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3476_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3476_, 1, v___x_3475_);
                v___x_3477_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3423_, v___x_3476_);
                v___x_3478_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__84;
                v___x_3479_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__85);
                v___x_3480_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__86;
                v___x_3481_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3480_, v_currMacroScope_3267_);
                v___x_3482_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3252_, v___x_3478_);
                v___x_3483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3483_, 0, v___x_3482_);
                leanh::lean_ctor_set(v___x_3483_, 1, v___x_3317_);
                v___x_3484_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3484_, 0, v___x_3483_);
                leanh::lean_ctor_set(v___x_3484_, 1, v___x_3317_);
                v___x_3485_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3485_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3485_, 1, v___x_3479_);
                leanh::lean_ctor_set(v___x_3485_, 2, v___x_3481_);
                leanh::lean_ctor_set(v___x_3485_, 3, v___x_3484_);
                leanh::lean_inc(v___x_3477_);
                v___x_3486_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3450_,
                    v___x_3351_,
                    v___x_3452_,
                    v___x_3477_,
                    v___x_3299_,
                );
                v___x_3487_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3271_, v___x_3486_, v___x_3374_);
                v___x_3488_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3408_, v___x_3485_, v___x_3487_);
                v___x_3489_ = l_Lean_Syntax_node3(
                    v___x_3270_,
                    v___x_3428_,
                    v___x_3441_,
                    v___x_3488_,
                    v___x_3392_,
                );
                v___x_3490_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3271_, v___x_3477_, v___x_3489_);
                v___x_3491_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3408_, v___x_3422_, v___x_3490_);
                v___x_3492_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3403_,
                    v___x_3406_,
                    v___x_3278_,
                    v___x_3278_,
                    v___x_3342_,
                    v___x_3491_,
                );
                v___x_3493_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3401_, v___x_3492_);
                v___x_3494_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3399_,
                    v___x_3365_,
                    v___x_3278_,
                    v___x_3368_,
                    v___x_3493_,
                );
                v___x_3495_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3494_, v___x_3278_);
                v___x_3496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__88);
                v___x_3497_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__90;
                v___x_3498_ =
                    l_Lean_addMacroScope(v_quotContext_3266_, v___x_3497_, v_currMacroScope_3267_);
                v___x_3499_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3499_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3499_, 1, v___x_3496_);
                leanh::lean_ctor_set(v___x_3499_, 2, v___x_3498_);
                leanh::lean_ctor_set(v___x_3499_, 3, v___x_3317_);
                v___x_3500_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3403_,
                    v___x_3406_,
                    v___x_3278_,
                    v___x_3278_,
                    v___x_3342_,
                    v___x_3499_,
                );
                v___x_3501_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3401_, v___x_3500_);
                v___x_3502_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3399_,
                    v___x_3365_,
                    v___x_3278_,
                    v___x_3368_,
                    v___x_3501_,
                );
                v___x_3503_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3502_, v___x_3278_);
                v___x_3504_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__91;
                v___x_3505_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3279_, v___x_3504_);
                v___x_3506_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__92;
                v___x_3507_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3507_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3507_, 1, v___x_3506_);
                leanh::lean_inc(v___x_3352_);
                v___x_3508_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3505_, v___x_3507_, v___x_3352_);
                v___x_3509_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3361_, v___x_3508_, v___x_3278_);
                v___x_3510_ = l_Lean_Syntax_node6(
                    v___x_3270_,
                    v___x_3271_,
                    v___x_3397_,
                    v___x_3418_,
                    v___x_3474_,
                    v___x_3495_,
                    v___x_3503_,
                    v___x_3509_,
                );
                v___x_3511_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3359_, v___x_3510_);
                v___x_3512_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3356_, v___x_3357_, v___x_3511_);
                v___x_3513_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3347_,
                    v___x_3352_,
                    v___x_3278_,
                    v___x_3354_,
                    v___x_3512_,
                );
                v___x_3514_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3344_, v___x_3345_, v___x_3513_);
                v___x_3515_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__93;
                v___x_3516_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__94;
                v___x_3517_ =
                    l_Lean_Name_mkStr4(v___x_3245_, v___x_3246_, v___x_3515_, v___x_3516_);
                v___x_3518_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3517_, v___x_3278_, v___x_3278_);
                v___x_3519_ = l_Lean_Syntax_node4(
                    v___x_3270_,
                    v___x_3340_,
                    v___x_3342_,
                    v___x_3514_,
                    v___x_3518_,
                    v___x_3278_,
                );
                v___x_3520_ = l_Lean_Syntax_node5(
                    v___x_3270_,
                    v___x_3309_,
                    v___x_3311_,
                    v___x_3319_,
                    v___x_3338_,
                    v___x_3519_,
                    v___x_3278_,
                );
                v___x_3521_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3274_, v___x_3307_, v___x_3520_);
                v___x_3522_ =
                    l_Lean_Syntax_node2(v___x_3270_, v___x_3271_, v_snd_3262_, v___x_3521_);
                v___x_3523_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3523_, 0, v___x_3522_);
                leanh::lean_ctor_set(v___x_3523_, 1, v___y_3255_);
                return v___x_3523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___boxed(
    mut v___x_3528_: *mut leanh::LeanObject,
    mut v___x_3529_: *mut leanh::LeanObject,
    mut v___x_3530_: *mut leanh::LeanObject,
    mut v___x_3531_: *mut leanh::LeanObject,
    mut v___x_3532_: *mut leanh::LeanObject,
    mut v___x_3533_: *mut leanh::LeanObject,
    mut v___x_3534_: *mut leanh::LeanObject,
    mut v___x_3535_: *mut leanh::LeanObject,
    mut v_____x_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3539_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_3528_, v___x_3529_, v___x_3530_, v___x_3531_, v___x_3532_, v___x_3533_, v___x_3534_, v___x_3535_, v_____x_3536_, v___y_3537_, v___y_3538_);
    leanh::lean_dec_ref(v___y_3537_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(
    mut v___x_3540_: u8,
    mut v_____do__lift_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3541_, v___x_3540_);
    v___x_3545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3545_, 0, v___x_3544_);
    leanh::lean_ctor_set(v___x_3545_, 1, v___y_3543_);
    return v___x_3545_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1___boxed(
    mut v___x_3546_: *mut leanh::LeanObject,
    mut v_____do__lift_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_40021__boxed_3550_: u8 = 0;
    let mut v_res_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_40021__boxed_3550_ = (leanh::lean_unbox(v___x_3546_) as u8);
    v_res_3551_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_40021__boxed_3550_, v_____do__lift_3547_, v___y_3548_, v___y_3549_);
    leanh::lean_dec_ref(v___y_3548_);
    leanh::lean_dec(v_____do__lift_3547_);
    return v_res_3551_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0;
    v___x_3567_ = l_String_toRawSubstring_x27(v___x_3566_);
    return v___x_3567_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__11;
    v___x_3580_ = l_String_toRawSubstring_x27(v___x_3579_);
    return v___x_3580_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__25;
    v___x_3606_ = l_String_toRawSubstring_x27(v___x_3605_);
    return v___x_3606_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__30;
    v___x_3617_ = l_String_toRawSubstring_x27(v___x_3616_);
    return v___x_3617_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__34;
    v___x_3627_ = l_String_toRawSubstring_x27(v___x_3626_);
    return v___x_3627_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3638_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__40;
    v___x_3639_ = l_String_toRawSubstring_x27(v___x_3638_);
    return v___x_3639_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__44;
    v___x_3649_ = l_String_toRawSubstring_x27(v___x_3648_);
    return v___x_3649_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_Lean_Parser_Tactic_dsimpKind___closed__2;
    v___x_3660_ = l_String_toRawSubstring_x27(v___x_3659_);
    return v___x_3660_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3682_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__58;
    v___x_3683_ = l_String_toRawSubstring_x27(v___x_3682_);
    return v___x_3683_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3699_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65;
    v___x_3700_ = l_String_toRawSubstring_x27(v___x_3699_);
    return v___x_3700_;
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(
    mut v_x_3715_: *mut leanh::LeanObject,
    mut v_a_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v_quotContext_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut v_reuseFailAlloc_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_quotContext_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v_reuseFailAlloc_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_quotContext_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: u8 = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v_reuseFailAlloc_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__0;
                v___x_3730_ = l_Lean___aux__Init__Meta______macroRules__Lean__Parser__Syntax__addPrec__1___closed__1;
                v___x_3731_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__0;
                v___x_3732_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__1;
                leanh::lean_inc(v_x_3715_);
                v___x_3733_ = l_Lean_Syntax_isOfKind(v_x_3715_, v___x_3732_);
                if v___x_3733_ == 0 {
                    leanh::lean_dec(v_x_3715_);
                    v___x_3734_ = leanh::lean_box(1);
                    v___x_3735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3735_, 0, v___x_3734_);
                    leanh::lean_ctor_set(v___x_3735_, 1, v_a_3717_);
                    return v___x_3735_;
                } else {
                    v___x_3736_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3737_ = l_Lean_Syntax_getArg(v_x_3715_, v___x_3736_);
                    v___x_3738_ = leanh::lean_unsigned_to_nat(2);
                    v___x_3739_ = l_Lean_Syntax_getArg(v_x_3715_, v___x_3738_);
                    v___x_3740_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3741_ = l_Lean_Syntax_getArg(v_x_3715_, v___x_3740_);
                    v___x_3742_ = leanh::lean_unsigned_to_nat(6);
                    v___x_3743_ = l_Lean_Syntax_getArg(v_x_3715_, v___x_3742_);
                    v___x_3744_ = leanh::lean_unsigned_to_nat(8);
                    v___x_3745_ = l_Lean_Syntax_getArg(v_x_3715_, v___x_3744_);
                    leanh::lean_dec(v_x_3715_);
                    v___x_3746_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__0;
                    v___x_3747_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1;
                    v___x_3748_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__27;
                    v___x_3749_ = leanh::lean_box(0);
                    v___x_4311_ = l_Lean_Syntax_getOptional_x3f(v___x_3737_);
                    leanh::lean_dec(v___x_3737_);
                    if leanh::lean_obj_tag(v___x_4311_) == 0 {
                        v___x_4312_ = leanh::lean_box(0);
                        v___y_4172_ = v___x_4312_;
                        state = 7;
                        continue;
                    } else {
                        v_val_4313_ = leanh::lean_ctor_get(v___x_4311_, 0);
                        v_isSharedCheck_4320_ =
                            (!leanh::lean_is_exclusive(v___x_4311_)) as u8;
                        if v_isSharedCheck_4320_ == 0 {
                            v___x_4315_ = v___x_4311_;
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4313_);
                            leanh::lean_dec(v___x_4311_);
                            v___x_4315_ = leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_3720_ = leanh::lean_ctor_get(v___y_3719_, 0);
                v_a_3721_ = leanh::lean_ctor_get(v___y_3719_, 1);
                v_isSharedCheck_3728_ = (!leanh::lean_is_exclusive(v___y_3719_)) as u8;
                if v_isSharedCheck_3728_ == 0 {
                    v___x_3723_ = v___y_3719_;
                    v_isShared_3724_ = v_isSharedCheck_3728_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3721_);
                    leanh::lean_inc(v_a_3720_);
                    leanh::lean_dec(v___y_3719_);
                    v___x_3723_ = leanh::lean_box(0);
                    v_isShared_3724_ = v_isSharedCheck_3728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3726_;
            }
            4 => {
                leanh::lean_inc_ref_n(v___y_3763_, 2);
                v___x_3766_ = l_Array_append___redArg(v___y_3763_, v___y_3765_);
                leanh::lean_dec_ref(v___y_3765_);
                leanh::lean_inc_n(v___y_3764_, 9);
                leanh::lean_inc_n(v___y_3754_, 56);
                v___x_3767_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3767_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3767_, 1, v___y_3764_);
                leanh::lean_ctor_set(v___x_3767_, 2, v___x_3766_);
                v___x_3768_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3768_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3768_, 1, v___y_3764_);
                leanh::lean_ctor_set(v___x_3768_, 2, v___y_3763_);
                v___x_3769_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6;
                leanh::lean_inc_ref(v___y_3755_);
                v___x_3770_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_3755_, v___x_3769_);
                leanh::lean_inc_ref_n(v___x_3768_, 9);
                v___x_3771_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3770_, v___x_3768_);
                leanh::lean_inc_ref(v___y_3753_);
                v___x_3772_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3772_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3772_, 1, v___y_3753_);
                v___x_3773_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0;
                leanh::lean_inc_ref(v___y_3751_);
                v___x_3774_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_3751_, v___x_3773_);
                v___x_3775_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
                v___x_3776_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3776_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3776_, 1, v___x_3775_);
                v___x_3777_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1;
                v___x_3778_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3778_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3778_, 1, v___x_3777_);
                v___x_3779_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
                v___x_3780_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3780_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
                v___x_3782_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3782_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3782_, 1, v___x_3781_);
                leanh::lean_inc_ref_n(v___x_3782_, 5);
                leanh::lean_inc(v___x_3741_);
                leanh::lean_inc_ref_n(v___x_3776_, 5);
                v___x_3783_ = l_Lean_Syntax_node5(
                    v___y_3754_,
                    v___x_3774_,
                    v___x_3776_,
                    v___x_3778_,
                    v___x_3780_,
                    v___x_3741_,
                    v___x_3782_,
                );
                v___x_3784_ = l_Lean_Syntax_node1(v___y_3754_, v___y_3764_, v___x_3783_);
                v___x_3785_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3;
                v___x_3786_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3785_, v___x_3743_);
                v___x_3787_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5;
                v___x_3788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
                v___x_3789_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7;
                leanh::lean_inc_n(v___y_3757_, 6);
                leanh::lean_inc_n(v___y_3759_, 6);
                v___x_3790_ = l_Lean_addMacroScope(v___y_3759_, v___x_3789_, v___y_3757_);
                leanh::lean_inc_n(v___y_3762_, 6);
                v___x_3791_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3791_, 0, v___x_3747_);
                leanh::lean_ctor_set(v___x_3791_, 1, v___y_3762_);
                leanh::lean_inc_n(v___y_3760_, 7);
                v___x_3792_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3792_, 0, v___x_3791_);
                leanh::lean_ctor_set(v___x_3792_, 1, v___y_3760_);
                v___x_3793_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3793_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3793_, 1, v___x_3788_);
                leanh::lean_ctor_set(v___x_3793_, 2, v___x_3790_);
                leanh::lean_ctor_set(v___x_3793_, 3, v___x_3792_);
                v___x_3794_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3793_, v___x_3768_);
                v___x_3795_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9;
                v___x_3796_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10;
                v___x_3797_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
                v___x_3798_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13;
                v___x_3799_ = l_Lean_addMacroScope(v___y_3759_, v___x_3798_, v___y_3757_);
                v___x_3800_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14;
                v___x_3801_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3801_, 0, v___x_3800_);
                leanh::lean_ctor_set(v___x_3801_, 1, v___y_3762_);
                v___x_3802_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
                leanh::lean_ctor_set(v___x_3802_, 1, v___y_3760_);
                v___x_3803_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3803_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3803_, 1, v___x_3797_);
                leanh::lean_ctor_set(v___x_3803_, 2, v___x_3799_);
                leanh::lean_ctor_set(v___x_3803_, 3, v___x_3802_);
                v___x_3804_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3803_, v___x_3768_);
                v___x_3805_ = l_Lean_Syntax_node1(v___y_3754_, v___y_3764_, v___x_3804_);
                v___x_3806_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3796_,
                    v___x_3776_,
                    v___x_3805_,
                    v___x_3782_,
                );
                v___x_3807_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15;
                v___x_3808_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3808_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                leanh::lean_inc_ref_n(v___x_3808_, 3);
                v___x_3809_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3795_, v___x_3806_, v___x_3808_);
                v___x_3810_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17;
                v___x_3811_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18;
                v___x_3812_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3812_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3812_, 1, v___x_3811_);
                v___x_3813_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19;
                v___x_3814_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3814_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3814_, 1, v___x_3813_);
                v___x_3815_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3748_, v___x_3814_);
                v___x_3816_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3810_, v___x_3812_, v___x_3815_);
                v___x_3817_ = l_Lean_Syntax_node1(v___y_3754_, v___y_3764_, v___x_3816_);
                v___x_3818_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3796_,
                    v___x_3776_,
                    v___x_3817_,
                    v___x_3782_,
                );
                v___x_3819_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3795_, v___x_3818_, v___x_3808_);
                v___x_3820_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20;
                v___x_3821_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3821_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3821_, 1, v___x_3820_);
                v___x_3822_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3748_, v___x_3821_);
                v___x_3823_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3785_, v___x_3822_);
                v___x_3824_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22;
                v___x_3825_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24;
                v___x_3826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__26);
                v___x_3827_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__27;
                v___x_3828_ = l_Lean_addMacroScope(v___y_3759_, v___x_3827_, v___y_3757_);
                v___x_3829_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__28;
                v___x_3830_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                leanh::lean_ctor_set(v___x_3830_, 1, v___y_3762_);
                v___x_3831_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3831_, 0, v___x_3830_);
                leanh::lean_ctor_set(v___x_3831_, 1, v___y_3760_);
                v___x_3832_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3832_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3832_, 1, v___x_3826_);
                leanh::lean_ctor_set(v___x_3832_, 2, v___x_3828_);
                leanh::lean_ctor_set(v___x_3832_, 3, v___x_3831_);
                v___x_3833_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3832_, v___x_3768_);
                v___x_3834_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29;
                v___x_3835_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3835_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3835_, 1, v___x_3834_);
                v___x_3836_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
                v___x_3837_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32;
                v___x_3838_ = l_Lean_addMacroScope(v___y_3759_, v___x_3837_, v___y_3757_);
                v___x_3839_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33;
                v___x_3840_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3840_, 0, v___x_3839_);
                leanh::lean_ctor_set(v___x_3840_, 1, v___y_3762_);
                v___x_3841_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                leanh::lean_ctor_set(v___x_3841_, 1, v___y_3760_);
                v___x_3842_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3842_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3842_, 1, v___x_3836_);
                leanh::lean_ctor_set(v___x_3842_, 2, v___x_3838_);
                leanh::lean_ctor_set(v___x_3842_, 3, v___x_3841_);
                v___x_3843_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3842_, v___x_3768_);
                v___x_3844_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
                v___x_3845_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36;
                v___x_3846_ = l_Lean_addMacroScope(v___y_3759_, v___x_3845_, v___y_3757_);
                v___x_3847_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37;
                v___x_3848_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3848_, 0, v___x_3847_);
                leanh::lean_ctor_set(v___x_3848_, 1, v___y_3762_);
                v___x_3849_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3849_, 0, v___x_3848_);
                leanh::lean_ctor_set(v___x_3849_, 1, v___y_3760_);
                v___x_3850_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3850_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3850_, 1, v___x_3844_);
                leanh::lean_ctor_set(v___x_3850_, 2, v___x_3846_);
                leanh::lean_ctor_set(v___x_3850_, 3, v___x_3849_);
                v___x_3851_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3850_, v___x_3768_);
                leanh::lean_inc_ref(v___x_3835_);
                v___x_3852_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3825_,
                    v___x_3843_,
                    v___x_3835_,
                    v___x_3851_,
                );
                v___x_3853_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3825_,
                    v___x_3833_,
                    v___x_3835_,
                    v___x_3852_,
                );
                v___x_3854_ = l_Lean_Syntax_node1(v___y_3754_, v___y_3764_, v___x_3853_);
                v___x_3855_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3796_,
                    v___x_3776_,
                    v___x_3854_,
                    v___x_3782_,
                );
                v___x_3856_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38;
                v___x_3857_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3857_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3857_, 1, v___x_3856_);
                v___x_3858_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3824_, v___x_3855_, v___x_3857_);
                v___x_3859_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39;
                v___x_3860_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3860_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3860_, 1, v___x_3859_);
                v___x_3861_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3748_, v___x_3860_);
                v___x_3862_ = l_Lean_Syntax_node1(v___y_3754_, v___x_3785_, v___x_3861_);
                v___x_3863_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___y_3764_,
                    v___x_3823_,
                    v___x_3858_,
                    v___x_3862_,
                );
                v___x_3864_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3796_,
                    v___x_3776_,
                    v___x_3863_,
                    v___x_3782_,
                );
                v___x_3865_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3795_, v___x_3864_, v___x_3808_);
                v___x_3866_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
                v___x_3867_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42;
                v___x_3868_ = l_Lean_addMacroScope(v___y_3759_, v___x_3867_, v___y_3757_);
                v___x_3869_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43;
                v___x_3870_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
                leanh::lean_ctor_set(v___x_3870_, 1, v___y_3762_);
                v___x_3871_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3871_, 0, v___x_3870_);
                leanh::lean_ctor_set(v___x_3871_, 1, v___y_3760_);
                v___x_3872_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3872_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3872_, 1, v___x_3866_);
                leanh::lean_ctor_set(v___x_3872_, 2, v___x_3868_);
                leanh::lean_ctor_set(v___x_3872_, 3, v___x_3871_);
                v___x_3873_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3787_, v___x_3872_, v___x_3768_);
                v___x_3874_ = l_Lean_Syntax_node1(v___y_3754_, v___y_3764_, v___x_3873_);
                v___x_3875_ = l_Lean_Syntax_node3(
                    v___y_3754_,
                    v___x_3796_,
                    v___x_3776_,
                    v___x_3874_,
                    v___x_3782_,
                );
                v___x_3876_ =
                    l_Lean_Syntax_node2(v___y_3754_, v___x_3795_, v___x_3875_, v___x_3808_);
                v___x_3877_ = l_Lean_Syntax_node6(
                    v___y_3754_,
                    v___y_3764_,
                    v___x_3786_,
                    v___x_3794_,
                    v___x_3809_,
                    v___x_3819_,
                    v___x_3865_,
                    v___x_3876_,
                );
                v___x_3878_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19;
                v___x_3879_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3879_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3879_, 1, v___x_3878_);
                v___x_3880_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
                v___x_3881_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46;
                v___x_3882_ = l_Lean_addMacroScope(v___y_3759_, v___x_3881_, v___y_3757_);
                v___x_3883_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3883_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3883_, 1, v___x_3880_);
                leanh::lean_ctor_set(v___x_3883_, 2, v___x_3882_);
                leanh::lean_ctor_set(v___x_3883_, 3, v___y_3760_);
                v___x_3884_ = leanh::lean_unsigned_to_nat(10);
                v___x_3885_ = lean_mk_empty_array_with_capacity(v___x_3884_);
                v___x_3886_ = lean_array_push(v___x_3885_, v___x_3767_);
                v___x_3887_ = lean_array_push(v___x_3886_, v___x_3768_);
                v___x_3888_ = lean_array_push(v___x_3887_, v___x_3771_);
                v___x_3889_ = lean_array_push(v___x_3888_, v___x_3772_);
                v___x_3890_ = lean_array_push(v___x_3889_, v___x_3768_);
                v___x_3891_ = lean_array_push(v___x_3890_, v___x_3784_);
                v___x_3892_ = lean_array_push(v___x_3891_, v___x_3768_);
                v___x_3893_ = lean_array_push(v___x_3892_, v___x_3877_);
                v___x_3894_ = lean_array_push(v___x_3893_, v___x_3879_);
                v___x_3895_ = lean_array_push(v___x_3894_, v___x_3883_);
                leanh::lean_inc(v___y_3752_);
                v___x_3896_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3896_, 0, v___y_3754_);
                leanh::lean_ctor_set(v___x_3896_, 1, v___y_3752_);
                leanh::lean_ctor_set(v___x_3896_, 2, v___x_3895_);
                v___x_3897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3897_, 0, v___y_3758_);
                leanh::lean_ctor_set(v___x_3897_, 1, v___x_3896_);
                v___x_3898_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3898_, 0, v___y_3756_);
                leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                v___x_3899_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_3729_, v___x_3730_, v___x_3741_, v___x_3746_, v___x_3747_, v___x_3745_, v___x_3749_, v___x_3731_, v___x_3898_, v_a_3716_, v___y_3761_);
                v___y_3719_ = v___x_3899_;
                state = 1;
                continue;
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_3909_, 2);
                v___x_3916_ = l_Array_append___redArg(v___y_3909_, v___y_3915_);
                leanh::lean_dec_ref(v___y_3915_);
                leanh::lean_inc_n(v___y_3908_, 9);
                leanh::lean_inc_n(v___y_3902_, 53);
                v___x_3917_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3917_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3917_, 1, v___y_3908_);
                leanh::lean_ctor_set(v___x_3917_, 2, v___x_3916_);
                v___x_3918_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3918_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3918_, 1, v___y_3908_);
                leanh::lean_ctor_set(v___x_3918_, 2, v___y_3909_);
                v___x_3919_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6;
                leanh::lean_inc_ref(v___y_3910_);
                v___x_3920_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_3910_, v___x_3919_);
                leanh::lean_inc_ref_n(v___x_3918_, 8);
                v___x_3921_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3920_, v___x_3918_);
                leanh::lean_inc_ref(v___y_3904_);
                v___x_3922_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3922_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3922_, 1, v___y_3904_);
                v___x_3923_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0;
                leanh::lean_inc_ref(v___y_3912_);
                v___x_3924_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_3912_, v___x_3923_);
                v___x_3925_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
                v___x_3926_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3926_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                v___x_3927_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1;
                v___x_3928_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3928_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3928_, 1, v___x_3927_);
                v___x_3929_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
                v___x_3930_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3930_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3930_, 1, v___x_3929_);
                v___x_3931_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
                v___x_3932_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3932_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3932_, 1, v___x_3931_);
                leanh::lean_inc_ref_n(v___x_3932_, 5);
                leanh::lean_inc(v___x_3741_);
                leanh::lean_inc_ref_n(v___x_3926_, 5);
                v___x_3933_ = l_Lean_Syntax_node5(
                    v___y_3902_,
                    v___x_3924_,
                    v___x_3926_,
                    v___x_3928_,
                    v___x_3930_,
                    v___x_3741_,
                    v___x_3932_,
                );
                v___x_3934_ = l_Lean_Syntax_node1(v___y_3902_, v___y_3908_, v___x_3933_);
                v___x_3935_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3;
                v___x_3936_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3935_, v___x_3743_);
                v___x_3937_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5;
                v___x_3938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
                v___x_3939_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7;
                leanh::lean_inc_n(v___y_3903_, 5);
                leanh::lean_inc_n(v___y_3901_, 5);
                v___x_3940_ = l_Lean_addMacroScope(v___y_3901_, v___x_3939_, v___y_3903_);
                leanh::lean_inc_n(v___y_3911_, 5);
                v___x_3941_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3941_, 0, v___x_3747_);
                leanh::lean_ctor_set(v___x_3941_, 1, v___y_3911_);
                leanh::lean_inc_n(v___y_3907_, 6);
                v___x_3942_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3942_, 0, v___x_3941_);
                leanh::lean_ctor_set(v___x_3942_, 1, v___y_3907_);
                v___x_3943_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3943_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3943_, 1, v___x_3938_);
                leanh::lean_ctor_set(v___x_3943_, 2, v___x_3940_);
                leanh::lean_ctor_set(v___x_3943_, 3, v___x_3942_);
                v___x_3944_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3937_, v___x_3943_, v___x_3918_);
                v___x_3945_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9;
                v___x_3946_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10;
                v___x_3947_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
                v___x_3948_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13;
                v___x_3949_ = l_Lean_addMacroScope(v___y_3901_, v___x_3948_, v___y_3903_);
                v___x_3950_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14;
                v___x_3951_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3951_, 0, v___x_3950_);
                leanh::lean_ctor_set(v___x_3951_, 1, v___y_3911_);
                v___x_3952_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3952_, 0, v___x_3951_);
                leanh::lean_ctor_set(v___x_3952_, 1, v___y_3907_);
                v___x_3953_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3953_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3953_, 1, v___x_3947_);
                leanh::lean_ctor_set(v___x_3953_, 2, v___x_3949_);
                leanh::lean_ctor_set(v___x_3953_, 3, v___x_3952_);
                v___x_3954_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3937_, v___x_3953_, v___x_3918_);
                v___x_3955_ = l_Lean_Syntax_node1(v___y_3902_, v___y_3908_, v___x_3954_);
                v___x_3956_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3946_,
                    v___x_3926_,
                    v___x_3955_,
                    v___x_3932_,
                );
                v___x_3957_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15;
                v___x_3958_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3958_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3958_, 1, v___x_3957_);
                leanh::lean_inc_ref_n(v___x_3958_, 3);
                v___x_3959_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3945_, v___x_3956_, v___x_3958_);
                v___x_3960_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17;
                v___x_3961_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18;
                v___x_3962_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3962_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3962_, 1, v___x_3961_);
                v___x_3963_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19;
                v___x_3964_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3964_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3748_, v___x_3964_);
                v___x_3966_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3960_, v___x_3962_, v___x_3965_);
                v___x_3967_ = l_Lean_Syntax_node1(v___y_3902_, v___y_3908_, v___x_3966_);
                v___x_3968_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3946_,
                    v___x_3926_,
                    v___x_3967_,
                    v___x_3932_,
                );
                v___x_3969_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3945_, v___x_3968_, v___x_3958_);
                v___x_3970_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20;
                v___x_3971_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3971_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3971_, 1, v___x_3970_);
                v___x_3972_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3748_, v___x_3971_);
                v___x_3973_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3935_, v___x_3972_);
                v___x_3974_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22;
                v___x_3975_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24;
                v___x_3976_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
                v___x_3977_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32;
                v___x_3978_ = l_Lean_addMacroScope(v___y_3901_, v___x_3977_, v___y_3903_);
                v___x_3979_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33;
                v___x_3980_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
                leanh::lean_ctor_set(v___x_3980_, 1, v___y_3911_);
                v___x_3981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3981_, 0, v___x_3980_);
                leanh::lean_ctor_set(v___x_3981_, 1, v___y_3907_);
                v___x_3982_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3982_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3982_, 1, v___x_3976_);
                leanh::lean_ctor_set(v___x_3982_, 2, v___x_3978_);
                leanh::lean_ctor_set(v___x_3982_, 3, v___x_3981_);
                v___x_3983_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3937_, v___x_3982_, v___x_3918_);
                v___x_3984_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29;
                v___x_3985_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3985_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3985_, 1, v___x_3984_);
                v___x_3986_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
                v___x_3987_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36;
                v___x_3988_ = l_Lean_addMacroScope(v___y_3901_, v___x_3987_, v___y_3903_);
                v___x_3989_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37;
                v___x_3990_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3990_, 0, v___x_3989_);
                leanh::lean_ctor_set(v___x_3990_, 1, v___y_3911_);
                v___x_3991_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3991_, 0, v___x_3990_);
                leanh::lean_ctor_set(v___x_3991_, 1, v___y_3907_);
                v___x_3992_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3992_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3992_, 1, v___x_3986_);
                leanh::lean_ctor_set(v___x_3992_, 2, v___x_3988_);
                leanh::lean_ctor_set(v___x_3992_, 3, v___x_3991_);
                v___x_3993_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3937_, v___x_3992_, v___x_3918_);
                v___x_3994_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3975_,
                    v___x_3983_,
                    v___x_3985_,
                    v___x_3993_,
                );
                v___x_3995_ = l_Lean_Syntax_node1(v___y_3902_, v___y_3908_, v___x_3994_);
                v___x_3996_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3946_,
                    v___x_3926_,
                    v___x_3995_,
                    v___x_3932_,
                );
                v___x_3997_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38;
                v___x_3998_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3998_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_3998_, 1, v___x_3997_);
                v___x_3999_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3974_, v___x_3996_, v___x_3998_);
                v___x_4000_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39;
                v___x_4001_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4001_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                v___x_4002_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3748_, v___x_4001_);
                v___x_4003_ = l_Lean_Syntax_node1(v___y_3902_, v___x_3935_, v___x_4002_);
                v___x_4004_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___y_3908_,
                    v___x_3973_,
                    v___x_3999_,
                    v___x_4003_,
                );
                v___x_4005_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3946_,
                    v___x_3926_,
                    v___x_4004_,
                    v___x_3932_,
                );
                v___x_4006_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3945_, v___x_4005_, v___x_3958_);
                v___x_4007_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__41);
                v___x_4008_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__42;
                v___x_4009_ = l_Lean_addMacroScope(v___y_3901_, v___x_4008_, v___y_3903_);
                v___x_4010_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__43;
                v___x_4011_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4011_, 0, v___x_4010_);
                leanh::lean_ctor_set(v___x_4011_, 1, v___y_3911_);
                v___x_4012_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                leanh::lean_ctor_set(v___x_4012_, 1, v___y_3907_);
                v___x_4013_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4013_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_4013_, 1, v___x_4007_);
                leanh::lean_ctor_set(v___x_4013_, 2, v___x_4009_);
                leanh::lean_ctor_set(v___x_4013_, 3, v___x_4012_);
                v___x_4014_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3937_, v___x_4013_, v___x_3918_);
                v___x_4015_ = l_Lean_Syntax_node1(v___y_3902_, v___y_3908_, v___x_4014_);
                v___x_4016_ = l_Lean_Syntax_node3(
                    v___y_3902_,
                    v___x_3946_,
                    v___x_3926_,
                    v___x_4015_,
                    v___x_3932_,
                );
                v___x_4017_ =
                    l_Lean_Syntax_node2(v___y_3902_, v___x_3945_, v___x_4016_, v___x_3958_);
                v___x_4018_ = l_Lean_Syntax_node6(
                    v___y_3902_,
                    v___y_3908_,
                    v___x_3936_,
                    v___x_3944_,
                    v___x_3959_,
                    v___x_3969_,
                    v___x_4006_,
                    v___x_4017_,
                );
                v___x_4019_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19;
                v___x_4020_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4020_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_4020_, 1, v___x_4019_);
                v___x_4021_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
                v___x_4022_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46;
                v___x_4023_ = l_Lean_addMacroScope(v___y_3901_, v___x_4022_, v___y_3903_);
                v___x_4024_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4024_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_4024_, 1, v___x_4021_);
                leanh::lean_ctor_set(v___x_4024_, 2, v___x_4023_);
                leanh::lean_ctor_set(v___x_4024_, 3, v___y_3907_);
                v___x_4025_ = leanh::lean_unsigned_to_nat(10);
                v___x_4026_ = lean_mk_empty_array_with_capacity(v___x_4025_);
                v___x_4027_ = lean_array_push(v___x_4026_, v___x_3917_);
                v___x_4028_ = lean_array_push(v___x_4027_, v___x_3918_);
                v___x_4029_ = lean_array_push(v___x_4028_, v___x_3921_);
                v___x_4030_ = lean_array_push(v___x_4029_, v___x_3922_);
                v___x_4031_ = lean_array_push(v___x_4030_, v___x_3918_);
                v___x_4032_ = lean_array_push(v___x_4031_, v___x_3934_);
                v___x_4033_ = lean_array_push(v___x_4032_, v___x_3918_);
                v___x_4034_ = lean_array_push(v___x_4033_, v___x_4018_);
                v___x_4035_ = lean_array_push(v___x_4034_, v___x_4020_);
                v___x_4036_ = lean_array_push(v___x_4035_, v___x_4024_);
                leanh::lean_inc(v___y_3906_);
                v___x_4037_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4037_, 0, v___y_3902_);
                leanh::lean_ctor_set(v___x_4037_, 1, v___y_3906_);
                leanh::lean_ctor_set(v___x_4037_, 2, v___x_4036_);
                v___x_4038_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4038_, 0, v___y_3914_);
                leanh::lean_ctor_set(v___x_4038_, 1, v___x_4037_);
                v___x_4039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4039_, 0, v___y_3913_);
                leanh::lean_ctor_set(v___x_4039_, 1, v___x_4038_);
                v___x_4040_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_3729_, v___x_3730_, v___x_3741_, v___x_3746_, v___x_3747_, v___x_3745_, v___x_3749_, v___x_3731_, v___x_4039_, v_a_3716_, v___y_3905_);
                v___y_3719_ = v___x_4040_;
                state = 1;
                continue;
            }
            6 => {
                leanh::lean_inc_ref_n(v___y_4045_, 2);
                v___x_4057_ = l_Array_append___redArg(v___y_4045_, v___y_4056_);
                leanh::lean_dec_ref(v___y_4056_);
                leanh::lean_inc_n(v___y_4048_, 8);
                leanh::lean_inc_n(v___y_4051_, 48);
                v___x_4058_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4058_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4058_, 1, v___y_4048_);
                leanh::lean_ctor_set(v___x_4058_, 2, v___x_4057_);
                v___x_4059_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4059_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4059_, 1, v___y_4048_);
                leanh::lean_ctor_set(v___x_4059_, 2, v___y_4045_);
                v___x_4060_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__6;
                leanh::lean_inc_ref(v___y_4046_);
                v___x_4061_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_4046_, v___x_4060_);
                leanh::lean_inc_ref_n(v___x_4059_, 7);
                v___x_4062_ = l_Lean_Syntax_node1(v___y_4051_, v___x_4061_, v___x_4059_);
                leanh::lean_inc_ref(v___y_4042_);
                v___x_4063_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4063_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4063_, 1, v___y_4042_);
                v___x_4064_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__0;
                leanh::lean_inc_ref(v___y_4054_);
                v___x_4065_ =
                    l_Lean_Name_mkStr4(v___x_3729_, v___x_3730_, v___y_4054_, v___x_4064_);
                v___x_4066_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
                v___x_4067_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4067_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
                v___x_4068_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__1;
                v___x_4069_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4069_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
                v___x_4070_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
                v___x_4071_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4071_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4071_, 1, v___x_4070_);
                v___x_4072_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
                v___x_4073_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4073_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4073_, 1, v___x_4072_);
                leanh::lean_inc_ref_n(v___x_4073_, 4);
                leanh::lean_inc(v___x_3741_);
                leanh::lean_inc_ref_n(v___x_4067_, 4);
                v___x_4074_ = l_Lean_Syntax_node5(
                    v___y_4051_,
                    v___x_4065_,
                    v___x_4067_,
                    v___x_4069_,
                    v___x_4071_,
                    v___x_3741_,
                    v___x_4073_,
                );
                v___x_4075_ = l_Lean_Syntax_node1(v___y_4051_, v___y_4048_, v___x_4074_);
                v___x_4076_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__3;
                v___x_4077_ = l_Lean_Syntax_node1(v___y_4051_, v___x_4076_, v___x_3743_);
                v___x_4078_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__5;
                v___x_4079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__6);
                v___x_4080_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__7;
                leanh::lean_inc_n(v___y_4052_, 4);
                leanh::lean_inc_n(v___y_4049_, 4);
                v___x_4081_ = l_Lean_addMacroScope(v___y_4049_, v___x_4080_, v___y_4052_);
                leanh::lean_inc_n(v___y_4055_, 4);
                v___x_4082_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4082_, 0, v___x_3747_);
                leanh::lean_ctor_set(v___x_4082_, 1, v___y_4055_);
                leanh::lean_inc_n(v___y_4047_, 5);
                v___x_4083_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4083_, 0, v___x_4082_);
                leanh::lean_ctor_set(v___x_4083_, 1, v___y_4047_);
                v___x_4084_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4084_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4084_, 1, v___x_4079_);
                leanh::lean_ctor_set(v___x_4084_, 2, v___x_4081_);
                leanh::lean_ctor_set(v___x_4084_, 3, v___x_4083_);
                v___x_4085_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4078_, v___x_4084_, v___x_4059_);
                v___x_4086_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__9;
                v___x_4087_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__10;
                v___x_4088_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__12);
                v___x_4089_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__13;
                v___x_4090_ = l_Lean_addMacroScope(v___y_4049_, v___x_4089_, v___y_4052_);
                v___x_4091_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__14;
                v___x_4092_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4092_, 0, v___x_4091_);
                leanh::lean_ctor_set(v___x_4092_, 1, v___y_4055_);
                v___x_4093_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
                leanh::lean_ctor_set(v___x_4093_, 1, v___y_4047_);
                v___x_4094_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4094_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4094_, 1, v___x_4088_);
                leanh::lean_ctor_set(v___x_4094_, 2, v___x_4090_);
                leanh::lean_ctor_set(v___x_4094_, 3, v___x_4093_);
                v___x_4095_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4078_, v___x_4094_, v___x_4059_);
                v___x_4096_ = l_Lean_Syntax_node1(v___y_4051_, v___y_4048_, v___x_4095_);
                v___x_4097_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___x_4087_,
                    v___x_4067_,
                    v___x_4096_,
                    v___x_4073_,
                );
                v___x_4098_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__15;
                v___x_4099_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4099_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4099_, 1, v___x_4098_);
                leanh::lean_inc_ref_n(v___x_4099_, 2);
                v___x_4100_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4086_, v___x_4097_, v___x_4099_);
                v___x_4101_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__17;
                v___x_4102_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__18;
                v___x_4103_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4103_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4103_, 1, v___x_4102_);
                v___x_4104_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__19;
                v___x_4105_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4105_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4105_, 1, v___x_4104_);
                v___x_4106_ = l_Lean_Syntax_node1(v___y_4051_, v___x_3748_, v___x_4105_);
                v___x_4107_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4101_, v___x_4103_, v___x_4106_);
                v___x_4108_ = l_Lean_Syntax_node1(v___y_4051_, v___y_4048_, v___x_4107_);
                v___x_4109_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___x_4087_,
                    v___x_4067_,
                    v___x_4108_,
                    v___x_4073_,
                );
                v___x_4110_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4086_, v___x_4109_, v___x_4099_);
                v___x_4111_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__20;
                v___x_4112_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4112_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4112_, 1, v___x_4111_);
                v___x_4113_ = l_Lean_Syntax_node1(v___y_4051_, v___x_3748_, v___x_4112_);
                v___x_4114_ = l_Lean_Syntax_node1(v___y_4051_, v___x_4076_, v___x_4113_);
                v___x_4115_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__22;
                v___x_4116_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__24;
                v___x_4117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__31);
                v___x_4118_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__32;
                v___x_4119_ = l_Lean_addMacroScope(v___y_4049_, v___x_4118_, v___y_4052_);
                v___x_4120_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__33;
                v___x_4121_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v___x_4120_);
                leanh::lean_ctor_set(v___x_4121_, 1, v___y_4055_);
                v___x_4122_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4122_, 0, v___x_4121_);
                leanh::lean_ctor_set(v___x_4122_, 1, v___y_4047_);
                v___x_4123_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4123_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4123_, 1, v___x_4117_);
                leanh::lean_ctor_set(v___x_4123_, 2, v___x_4119_);
                leanh::lean_ctor_set(v___x_4123_, 3, v___x_4122_);
                v___x_4124_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4078_, v___x_4123_, v___x_4059_);
                v___x_4125_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__29;
                v___x_4126_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4126_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                v___x_4127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__35);
                v___x_4128_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__36;
                v___x_4129_ = l_Lean_addMacroScope(v___y_4049_, v___x_4128_, v___y_4052_);
                v___x_4130_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__37;
                v___x_4131_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4131_, 0, v___x_4130_);
                leanh::lean_ctor_set(v___x_4131_, 1, v___y_4055_);
                v___x_4132_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4132_, 0, v___x_4131_);
                leanh::lean_ctor_set(v___x_4132_, 1, v___y_4047_);
                v___x_4133_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4133_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4133_, 1, v___x_4127_);
                leanh::lean_ctor_set(v___x_4133_, 2, v___x_4129_);
                leanh::lean_ctor_set(v___x_4133_, 3, v___x_4132_);
                v___x_4134_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4078_, v___x_4133_, v___x_4059_);
                v___x_4135_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___x_4116_,
                    v___x_4124_,
                    v___x_4126_,
                    v___x_4134_,
                );
                v___x_4136_ = l_Lean_Syntax_node1(v___y_4051_, v___y_4048_, v___x_4135_);
                v___x_4137_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___x_4087_,
                    v___x_4067_,
                    v___x_4136_,
                    v___x_4073_,
                );
                v___x_4138_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__38;
                v___x_4139_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4139_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4139_, 1, v___x_4138_);
                v___x_4140_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4115_, v___x_4137_, v___x_4139_);
                v___x_4141_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__39;
                v___x_4142_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4142_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4142_, 1, v___x_4141_);
                v___x_4143_ = l_Lean_Syntax_node1(v___y_4051_, v___x_3748_, v___x_4142_);
                v___x_4144_ = l_Lean_Syntax_node1(v___y_4051_, v___x_4076_, v___x_4143_);
                v___x_4145_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___y_4048_,
                    v___x_4114_,
                    v___x_4140_,
                    v___x_4144_,
                );
                v___x_4146_ = l_Lean_Syntax_node3(
                    v___y_4051_,
                    v___x_4087_,
                    v___x_4067_,
                    v___x_4145_,
                    v___x_4073_,
                );
                v___x_4147_ =
                    l_Lean_Syntax_node2(v___y_4051_, v___x_4086_, v___x_4146_, v___x_4099_);
                v___x_4148_ = l_Lean_Syntax_node5(
                    v___y_4051_,
                    v___y_4048_,
                    v___x_4077_,
                    v___x_4085_,
                    v___x_4100_,
                    v___x_4110_,
                    v___x_4147_,
                );
                v___x_4149_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__19;
                v___x_4150_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4150_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4150_, 1, v___x_4149_);
                v___x_4151_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__45);
                v___x_4152_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__46;
                v___x_4153_ = l_Lean_addMacroScope(v___y_4049_, v___x_4152_, v___y_4052_);
                v___x_4154_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4154_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4154_, 1, v___x_4151_);
                leanh::lean_ctor_set(v___x_4154_, 2, v___x_4153_);
                leanh::lean_ctor_set(v___x_4154_, 3, v___y_4047_);
                v___x_4155_ = leanh::lean_unsigned_to_nat(10);
                v___x_4156_ = lean_mk_empty_array_with_capacity(v___x_4155_);
                v___x_4157_ = lean_array_push(v___x_4156_, v___x_4058_);
                v___x_4158_ = lean_array_push(v___x_4157_, v___x_4059_);
                v___x_4159_ = lean_array_push(v___x_4158_, v___x_4062_);
                v___x_4160_ = lean_array_push(v___x_4159_, v___x_4063_);
                v___x_4161_ = lean_array_push(v___x_4160_, v___x_4059_);
                v___x_4162_ = lean_array_push(v___x_4161_, v___x_4075_);
                v___x_4163_ = lean_array_push(v___x_4162_, v___x_4059_);
                v___x_4164_ = lean_array_push(v___x_4163_, v___x_4148_);
                v___x_4165_ = lean_array_push(v___x_4164_, v___x_4150_);
                v___x_4166_ = lean_array_push(v___x_4165_, v___x_4154_);
                leanh::lean_inc(v___y_4053_);
                v___x_4167_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4167_, 0, v___y_4051_);
                leanh::lean_ctor_set(v___x_4167_, 1, v___y_4053_);
                leanh::lean_ctor_set(v___x_4167_, 2, v___x_4166_);
                v___x_4168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4168_, 0, v___y_4050_);
                leanh::lean_ctor_set(v___x_4168_, 1, v___x_4167_);
                v___x_4169_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4169_, 0, v___y_4043_);
                leanh::lean_ctor_set(v___x_4169_, 1, v___x_4168_);
                v___x_4170_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2(v___x_3729_, v___x_3730_, v___x_3741_, v___x_3746_, v___x_3747_, v___x_3745_, v___x_3749_, v___x_3731_, v___x_4169_, v_a_3716_, v___y_4044_);
                v___y_3719_ = v___x_4170_;
                state = 1;
                continue;
            }
            7 => {
                v___x_4173_ = l_Lean_Syntax_isNone(v___x_3739_);
                if v___x_4173_ == 0 {
                    v___x_4174_ = l_Lean_Syntax_getArg(v___x_3739_, v___x_3736_);
                    leanh::lean_dec(v___x_3739_);
                    v___x_4175_ = l_Lean_Syntax_getKind(v___x_4174_);
                    v___x_4176_ = l_Lean_Parser_Tactic_simpAllKind___closed__1;
                    v___x_4177_ = lean_name_eq(v___x_4175_, v___x_4176_);
                    leanh::lean_dec(v___x_4175_);
                    if v___x_4177_ == 0 {
                        v_quotContext_4178_ = leanh::lean_ctor_get(v_a_3716_, 1);
                        v_currMacroScope_4179_ = leanh::lean_ctor_get(v_a_3716_, 2);
                        v_ref_4180_ = leanh::lean_ctor_get(v_a_3716_, 5);
                        v___x_4181_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_4177_, v_ref_4180_, v_a_3716_, v_a_3717_);
                        v_a_4182_ = leanh::lean_ctor_get(v___x_4181_, 0);
                        v_a_4183_ = leanh::lean_ctor_get(v___x_4181_, 1);
                        v_isSharedCheck_4221_ =
                            (!leanh::lean_is_exclusive(v___x_4181_)) as u8;
                        if v_isSharedCheck_4221_ == 0 {
                            v___x_4185_ = v___x_4181_;
                            v_isShared_4186_ = v_isSharedCheck_4221_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4183_);
                            leanh::lean_inc(v_a_4182_);
                            leanh::lean_dec(v___x_4181_);
                            v___x_4185_ = leanh::lean_box(0);
                            v_isShared_4186_ = v_isSharedCheck_4221_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_quotContext_4222_ = leanh::lean_ctor_get(v_a_3716_, 1);
                        v_currMacroScope_4223_ = leanh::lean_ctor_get(v_a_3716_, 2);
                        v_ref_4224_ = leanh::lean_ctor_get(v_a_3716_, 5);
                        v___x_4225_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_4224_, v_a_3716_, v_a_3717_);
                        v_a_4226_ = leanh::lean_ctor_get(v___x_4225_, 0);
                        v_a_4227_ = leanh::lean_ctor_get(v___x_4225_, 1);
                        v_isSharedCheck_4265_ =
                            (!leanh::lean_is_exclusive(v___x_4225_)) as u8;
                        if v_isSharedCheck_4265_ == 0 {
                            v___x_4229_ = v___x_4225_;
                            v_isShared_4230_ = v_isSharedCheck_4265_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4227_);
                            leanh::lean_inc(v_a_4226_);
                            leanh::lean_dec(v___x_4225_);
                            v___x_4229_ = leanh::lean_box(0);
                            v_isShared_4230_ = v_isSharedCheck_4265_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3739_);
                    v_quotContext_4266_ = leanh::lean_ctor_get(v_a_3716_, 1);
                    v_currMacroScope_4267_ = leanh::lean_ctor_get(v_a_3716_, 2);
                    v_ref_4268_ = leanh::lean_ctor_get(v_a_3716_, 5);
                    v___x_4269_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_4268_, v_a_3716_, v_a_3717_);
                    v_a_4270_ = leanh::lean_ctor_get(v___x_4269_, 0);
                    v_a_4271_ = leanh::lean_ctor_get(v___x_4269_, 1);
                    v_isSharedCheck_4310_ = (!leanh::lean_is_exclusive(v___x_4269_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4273_ = v___x_4269_;
                        v_isShared_4274_ = v_isSharedCheck_4310_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4271_);
                        leanh::lean_inc(v_a_4270_);
                        leanh::lean_dec(v___x_4269_);
                        v___x_4273_ = leanh::lean_box(0);
                        v_isShared_4274_ = v_isSharedCheck_4310_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4187_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17;
                v___x_4188_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48;
                v___x_4189_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49;
                leanh::lean_inc(v_a_4182_);
                if v_isShared_4186_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4185_, 2);
                    leanh::lean_ctor_set(v___x_4185_, 1, v___x_4189_);
                    v___x_4191_ = v___x_4185_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4189_);
                    v___x_4191_ = v_reuseFailAlloc_4220_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4192_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__50);
                v___x_4193_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__51;
                leanh::lean_inc(v_currMacroScope_4179_);
                leanh::lean_inc(v_quotContext_4178_);
                v___x_4194_ =
                    l_Lean_addMacroScope(v_quotContext_4178_, v___x_4193_, v_currMacroScope_4179_);
                v___x_4195_ = leanh::lean_box(0);
                v___x_4196_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__54;
                leanh::lean_inc(v_a_4182_);
                v___x_4197_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4197_, 0, v_a_4182_);
                leanh::lean_ctor_set(v___x_4197_, 1, v___x_4192_);
                leanh::lean_ctor_set(v___x_4197_, 2, v___x_4194_);
                leanh::lean_ctor_set(v___x_4197_, 3, v___x_4196_);
                leanh::lean_inc_ref(v___x_4191_);
                v___x_4198_ = l_Lean_Syntax_node3(
                    v_a_4182_,
                    v___x_4188_,
                    v___x_4191_,
                    v___x_4191_,
                    v___x_4197_,
                );
                v___x_4199_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__1(v___x_4177_, v_ref_4180_, v_a_3716_, v_a_4183_);
                v_a_4200_ = leanh::lean_ctor_get(v___x_4199_, 0);
                v_a_4201_ = leanh::lean_ctor_get(v___x_4199_, 1);
                v_isSharedCheck_4219_ = (!leanh::lean_is_exclusive(v___x_4199_)) as u8;
                if v_isSharedCheck_4219_ == 0 {
                    v___x_4203_ = v___x_4199_;
                    v_isShared_4204_ = v_isSharedCheck_4219_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4201_);
                    leanh::lean_inc(v_a_4200_);
                    leanh::lean_dec(v___x_4199_);
                    v___x_4203_ = leanh::lean_box(0);
                    v_isShared_4204_ = v_isSharedCheck_4219_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4205_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__55;
                leanh::lean_inc(v_a_4200_);
                if v_isShared_4204_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4203_, 2);
                    leanh::lean_ctor_set(v___x_4203_, 1, v___x_4205_);
                    v___x_4207_ = v___x_4203_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v___x_4205_);
                    v___x_4207_ = v_reuseFailAlloc_4218_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4208_ = l_Lean_Syntax_node1(v_a_4200_, v___x_3748_, v___x_4207_);
                v___x_4209_ = l_Lean_SourceInfo_fromRef(v_ref_4180_, v___x_4177_);
                v___x_4210_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0;
                v___x_4211_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56;
                v___x_4212_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57;
                v___x_4213_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
                v___x_4214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
                if leanh::lean_obj_tag(v___y_4172_) == 1 {
                    v_val_4215_ = leanh::lean_ctor_get(v___y_4172_, 0);
                    leanh::lean_inc(v_val_4215_);
                    leanh::lean_dec_ref_known(v___y_4172_, 1);
                    v___x_4216_ = l_Array_mkArray1___redArg(v_val_4215_);
                    leanh::lean_inc(v_currMacroScope_4179_);
                    leanh::lean_inc(v_quotContext_4178_);
                    v___y_3901_ = v_quotContext_4178_;
                    v___y_3902_ = v___x_4209_;
                    v___y_3903_ = v_currMacroScope_4179_;
                    v___y_3904_ = v___x_4211_;
                    v___y_3905_ = v_a_4201_;
                    v___y_3906_ = v___x_4212_;
                    v___y_3907_ = v___x_4195_;
                    v___y_3908_ = v___x_4213_;
                    v___y_3909_ = v___x_4214_;
                    v___y_3910_ = v___x_4187_;
                    v___y_3911_ = v___x_4195_;
                    v___y_3912_ = v___x_4210_;
                    v___y_3913_ = v___x_4198_;
                    v___y_3914_ = v___x_4208_;
                    v___y_3915_ = v___x_4216_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4172_);
                    v___x_4217_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31;
                    leanh::lean_inc(v_currMacroScope_4179_);
                    leanh::lean_inc(v_quotContext_4178_);
                    v___y_3901_ = v_quotContext_4178_;
                    v___y_3902_ = v___x_4209_;
                    v___y_3903_ = v_currMacroScope_4179_;
                    v___y_3904_ = v___x_4211_;
                    v___y_3905_ = v_a_4201_;
                    v___y_3906_ = v___x_4212_;
                    v___y_3907_ = v___x_4195_;
                    v___y_3908_ = v___x_4213_;
                    v___y_3909_ = v___x_4214_;
                    v___y_3910_ = v___x_4187_;
                    v___y_3911_ = v___x_4195_;
                    v___y_3912_ = v___x_4210_;
                    v___y_3913_ = v___x_4198_;
                    v___y_3914_ = v___x_4208_;
                    v___y_3915_ = v___x_4217_;
                    state = 5;
                    continue;
                }
            }
            12 => {
                v___x_4231_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17;
                v___x_4232_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48;
                v___x_4233_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49;
                leanh::lean_inc(v_a_4226_);
                if v_isShared_4230_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4229_, 2);
                    leanh::lean_ctor_set(v___x_4229_, 1, v___x_4233_);
                    v___x_4235_ = v___x_4229_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4233_);
                    v___x_4235_ = v_reuseFailAlloc_4264_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4236_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__59);
                v___x_4237_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__60;
                leanh::lean_inc(v_currMacroScope_4223_);
                leanh::lean_inc(v_quotContext_4222_);
                v___x_4238_ =
                    l_Lean_addMacroScope(v_quotContext_4222_, v___x_4237_, v_currMacroScope_4223_);
                v___x_4239_ = leanh::lean_box(0);
                v___x_4240_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__63;
                leanh::lean_inc(v_a_4226_);
                v___x_4241_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4241_, 0, v_a_4226_);
                leanh::lean_ctor_set(v___x_4241_, 1, v___x_4236_);
                leanh::lean_ctor_set(v___x_4241_, 2, v___x_4238_);
                leanh::lean_ctor_set(v___x_4241_, 3, v___x_4240_);
                leanh::lean_inc_ref(v___x_4235_);
                v___x_4242_ = l_Lean_Syntax_node3(
                    v_a_4226_,
                    v___x_4232_,
                    v___x_4235_,
                    v___x_4235_,
                    v___x_4241_,
                );
                v___x_4243_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_4224_, v_a_3716_, v_a_4227_);
                v_a_4244_ = leanh::lean_ctor_get(v___x_4243_, 0);
                v_a_4245_ = leanh::lean_ctor_get(v___x_4243_, 1);
                v_isSharedCheck_4263_ = (!leanh::lean_is_exclusive(v___x_4243_)) as u8;
                if v_isSharedCheck_4263_ == 0 {
                    v___x_4247_ = v___x_4243_;
                    v_isShared_4248_ = v_isSharedCheck_4263_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4245_);
                    leanh::lean_inc(v_a_4244_);
                    leanh::lean_dec(v___x_4243_);
                    v___x_4247_ = leanh::lean_box(0);
                    v_isShared_4248_ = v_isSharedCheck_4263_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4249_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__64;
                leanh::lean_inc(v_a_4244_);
                if v_isShared_4248_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4247_, 2);
                    leanh::lean_ctor_set(v___x_4247_, 1, v___x_4249_);
                    v___x_4251_ = v___x_4247_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4262_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4262_, 1, v___x_4249_);
                    v___x_4251_ = v_reuseFailAlloc_4262_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4252_ = l_Lean_Syntax_node1(v_a_4244_, v___x_3748_, v___x_4251_);
                v___x_4253_ = l_Lean_SourceInfo_fromRef(v_ref_4224_, v___x_4173_);
                v___x_4254_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0;
                v___x_4255_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56;
                v___x_4256_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57;
                v___x_4257_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
                v___x_4258_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
                if leanh::lean_obj_tag(v___y_4172_) == 1 {
                    v_val_4259_ = leanh::lean_ctor_get(v___y_4172_, 0);
                    leanh::lean_inc(v_val_4259_);
                    leanh::lean_dec_ref_known(v___y_4172_, 1);
                    v___x_4260_ = l_Array_mkArray1___redArg(v_val_4259_);
                    leanh::lean_inc(v_currMacroScope_4223_);
                    leanh::lean_inc(v_quotContext_4222_);
                    v___y_4042_ = v___x_4255_;
                    v___y_4043_ = v___x_4242_;
                    v___y_4044_ = v_a_4245_;
                    v___y_4045_ = v___x_4258_;
                    v___y_4046_ = v___x_4231_;
                    v___y_4047_ = v___x_4239_;
                    v___y_4048_ = v___x_4257_;
                    v___y_4049_ = v_quotContext_4222_;
                    v___y_4050_ = v___x_4252_;
                    v___y_4051_ = v___x_4253_;
                    v___y_4052_ = v_currMacroScope_4223_;
                    v___y_4053_ = v___x_4256_;
                    v___y_4054_ = v___x_4254_;
                    v___y_4055_ = v___x_4239_;
                    v___y_4056_ = v___x_4260_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4172_);
                    v___x_4261_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31;
                    leanh::lean_inc(v_currMacroScope_4223_);
                    leanh::lean_inc(v_quotContext_4222_);
                    v___y_4042_ = v___x_4255_;
                    v___y_4043_ = v___x_4242_;
                    v___y_4044_ = v_a_4245_;
                    v___y_4045_ = v___x_4258_;
                    v___y_4046_ = v___x_4231_;
                    v___y_4047_ = v___x_4239_;
                    v___y_4048_ = v___x_4257_;
                    v___y_4049_ = v_quotContext_4222_;
                    v___y_4050_ = v___x_4252_;
                    v___y_4051_ = v___x_4253_;
                    v___y_4052_ = v_currMacroScope_4223_;
                    v___y_4053_ = v___x_4256_;
                    v___y_4054_ = v___x_4254_;
                    v___y_4055_ = v___x_4239_;
                    v___y_4056_ = v___x_4261_;
                    state = 6;
                    continue;
                }
            }
            16 => {
                v___x_4275_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__17;
                v___x_4276_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__48;
                v___x_4277_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__49;
                leanh::lean_inc(v_a_4270_);
                if v_isShared_4274_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4273_, 2);
                    leanh::lean_ctor_set(v___x_4273_, 1, v___x_4277_);
                    v___x_4279_ = v___x_4273_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 1, v___x_4277_);
                    v___x_4279_ = v_reuseFailAlloc_4309_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__66);
                v___x_4281_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__67;
                leanh::lean_inc(v_currMacroScope_4267_);
                leanh::lean_inc(v_quotContext_4266_);
                v___x_4282_ =
                    l_Lean_addMacroScope(v_quotContext_4266_, v___x_4281_, v_currMacroScope_4267_);
                v___x_4283_ = leanh::lean_box(0);
                v___x_4284_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__70;
                leanh::lean_inc(v_a_4270_);
                v___x_4285_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4285_, 0, v_a_4270_);
                leanh::lean_ctor_set(v___x_4285_, 1, v___x_4280_);
                leanh::lean_ctor_set(v___x_4285_, 2, v___x_4282_);
                leanh::lean_ctor_set(v___x_4285_, 3, v___x_4284_);
                leanh::lean_inc_ref(v___x_4279_);
                v___x_4286_ = l_Lean_Syntax_node3(
                    v_a_4270_,
                    v___x_4276_,
                    v___x_4279_,
                    v___x_4279_,
                    v___x_4285_,
                );
                v___x_4287_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__0(v_ref_4268_, v_a_3716_, v_a_4271_);
                v_a_4288_ = leanh::lean_ctor_get(v___x_4287_, 0);
                v_a_4289_ = leanh::lean_ctor_get(v___x_4287_, 1);
                v_isSharedCheck_4308_ = (!leanh::lean_is_exclusive(v___x_4287_)) as u8;
                if v_isSharedCheck_4308_ == 0 {
                    v___x_4291_ = v___x_4287_;
                    v_isShared_4292_ = v_isSharedCheck_4308_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4289_);
                    leanh::lean_inc(v_a_4288_);
                    leanh::lean_dec(v___x_4287_);
                    v___x_4291_ = leanh::lean_box(0);
                    v_isShared_4292_ = v_isSharedCheck_4308_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4293_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__71;
                leanh::lean_inc(v_a_4288_);
                if v_isShared_4292_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4291_, 2);
                    leanh::lean_ctor_set(v___x_4291_, 1, v___x_4293_);
                    v___x_4295_ = v___x_4291_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4307_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 1, v___x_4293_);
                    v___x_4295_ = v_reuseFailAlloc_4307_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_4296_ = l_Lean_Syntax_node1(v_a_4288_, v___x_3748_, v___x_4295_);
                v___x_4297_ = 0;
                v___x_4298_ = l_Lean_SourceInfo_fromRef(v_ref_4268_, v___x_4297_);
                v___x_4299_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__0;
                v___x_4300_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__56;
                v___x_4301_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__57;
                v___x_4302_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
                v___x_4303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__7);
                if leanh::lean_obj_tag(v___y_4172_) == 1 {
                    v_val_4304_ = leanh::lean_ctor_get(v___y_4172_, 0);
                    leanh::lean_inc(v_val_4304_);
                    leanh::lean_dec_ref_known(v___y_4172_, 1);
                    v___x_4305_ = l_Array_mkArray1___redArg(v_val_4304_);
                    leanh::lean_inc(v_quotContext_4266_);
                    leanh::lean_inc(v_currMacroScope_4267_);
                    v___y_3751_ = v___x_4299_;
                    v___y_3752_ = v___x_4301_;
                    v___y_3753_ = v___x_4300_;
                    v___y_3754_ = v___x_4298_;
                    v___y_3755_ = v___x_4275_;
                    v___y_3756_ = v___x_4286_;
                    v___y_3757_ = v_currMacroScope_4267_;
                    v___y_3758_ = v___x_4296_;
                    v___y_3759_ = v_quotContext_4266_;
                    v___y_3760_ = v___x_4283_;
                    v___y_3761_ = v_a_4289_;
                    v___y_3762_ = v___x_4283_;
                    v___y_3763_ = v___x_4303_;
                    v___y_3764_ = v___x_4302_;
                    v___y_3765_ = v___x_4305_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4172_);
                    v___x_4306_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__31;
                    leanh::lean_inc(v_quotContext_4266_);
                    leanh::lean_inc(v_currMacroScope_4267_);
                    v___y_3751_ = v___x_4299_;
                    v___y_3752_ = v___x_4301_;
                    v___y_3753_ = v___x_4300_;
                    v___y_3754_ = v___x_4298_;
                    v___y_3755_ = v___x_4275_;
                    v___y_3756_ = v___x_4286_;
                    v___y_3757_ = v_currMacroScope_4267_;
                    v___y_3758_ = v___x_4296_;
                    v___y_3759_ = v_quotContext_4266_;
                    v___y_3760_ = v___x_4283_;
                    v___y_3761_ = v_a_4289_;
                    v___y_3762_ = v___x_4283_;
                    v___y_3763_ = v___x_4303_;
                    v___y_3764_ = v___x_4302_;
                    v___y_3765_ = v___x_4306_;
                    state = 4;
                    continue;
                }
            }
            20 => {
                if v_isShared_4316_ == 0 {
                    v___x_4318_ = v___x_4315_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_val_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_4172_ = v___x_4318_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___boxed(
    mut v_x_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
    mut v_a_4323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1(v_x_4321_, v_a_4322_, v_a_4323_);
    leanh::lean_dec_ref(v_a_4322_);
    return v_res_4324_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4336_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__3;
    v___x_4337_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4338_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4338_, 0, v___x_4337_);
    leanh::lean_ctor_set(v___x_4338_, 1, v___x_4336_);
    leanh::lean_ctor_set(v___x_4338_, 2, v___x_4335_);
    return v___x_4338_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4339_ = l_Lean_Parser_Tactic_discharger;
    v___x_4340_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__8;
    v___x_4341_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4341_, 0, v___x_4340_);
    leanh::lean_ctor_set(v___x_4341_, 1, v___x_4339_);
    return v___x_4341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__4,
    );
    v___x_4344_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4345_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4345_, 0, v___x_4344_);
    leanh::lean_ctor_set(v___x_4345_, 1, v___x_4343_);
    leanh::lean_ctor_set(v___x_4345_, 2, v___x_4342_);
    return v___x_4345_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__6,
    );
    v___x_4355_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4356_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4356_, 0, v___x_4355_);
    leanh::lean_ctor_set(v___x_4356_, 1, v___x_4354_);
    leanh::lean_ctor_set(v___x_4356_, 2, v___x_4353_);
    return v___x_4356_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = l_Lean_Parser_Tactic_simpLemma;
    v___x_4361_ = l_Lean_Parser_Tactic_simpErase;
    v___x_4362_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10;
    v___x_4363_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4363_, 0, v___x_4362_);
    leanh::lean_ctor_set(v___x_4363_, 1, v___x_4361_);
    leanh::lean_ctor_set(v___x_4363_, 2, v___x_4360_);
    return v___x_4363_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13,
    );
    v___x_4365_ = l_Lean_Parser_Tactic_simpStar;
    v___x_4366_ = l_Lean_Parser_Tactic_declareSimpLikeTactic___closed__10;
    v___x_4367_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    leanh::lean_ctor_set(v___x_4367_, 1, v___x_4365_);
    leanh::lean_ctor_set(v___x_4367_, 2, v___x_4364_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4372_: u8 = 0;
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4372_ = 0;
    v___x_4373_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__17;
    v___x_4374_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__15;
    v___x_4375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__14_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__14,
    );
    v___x_4376_ = leanh::lean_alloc_ctor(10, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_4376_, 0, v___x_4375_);
    leanh::lean_ctor_set(v___x_4376_, 1, v___x_4374_);
    leanh::lean_ctor_set(v___x_4376_, 2, v___x_4373_);
    leanh::lean_ctor_set_uint8(
        v___x_4376_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4372_,
    );
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__18_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__18,
    );
    v___x_4378_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__12;
    v___x_4379_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4380_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4380_, 0, v___x_4379_);
    leanh::lean_ctor_set(v___x_4380_, 1, v___x_4378_);
    leanh::lean_ctor_set(v___x_4380_, 2, v___x_4377_);
    return v___x_4380_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4383_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__20;
    v___x_4384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__19_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__19,
    );
    v___x_4385_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4386_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4386_, 0, v___x_4385_);
    leanh::lean_ctor_set(v___x_4386_, 1, v___x_4384_);
    leanh::lean_ctor_set(v___x_4386_, 2, v___x_4383_);
    return v___x_4386_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__21_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__21,
    );
    v___x_4388_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__8;
    v___x_4389_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4389_, 0, v___x_4388_);
    leanh::lean_ctor_set(v___x_4389_, 1, v___x_4387_);
    return v___x_4389_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22,
    );
    v___x_4391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__10_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__10,
    );
    v___x_4392_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4393_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4393_, 0, v___x_4392_);
    leanh::lean_ctor_set(v___x_4393_, 1, v___x_4391_);
    leanh::lean_ctor_set(v___x_4393_, 2, v___x_4390_);
    return v___x_4393_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9,
    );
    v___x_4395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__23_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__23,
    );
    v___x_4396_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4397_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4397_, 0, v___x_4396_);
    leanh::lean_ctor_set(v___x_4397_, 1, v___x_4395_);
    leanh::lean_ctor_set(v___x_4397_, 2, v___x_4394_);
    return v___x_4397_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__24_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__24,
    );
    v___x_4399_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4400_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__1;
    v___x_4401_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4401_, 0, v___x_4400_);
    leanh::lean_ctor_set(v___x_4401_, 1, v___x_4399_);
    leanh::lean_ctor_set(v___x_4401_, 2, v___x_4398_);
    return v___x_4401_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAutoUnfold() -> *mut leanh::LeanObject {
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4402_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__25_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__25,
    );
    return v___x_4402_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_()
-> *mut leanh::LeanObject {
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4404_ = l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_;
    v___x_4405_ = l_String_toRawSubstring_x27(v___x_4404_);
    return v___x_4405_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(
    mut v_s_4408_: *mut leanh::LeanObject,
    mut v_a_4409_: *mut leanh::LeanObject,
    mut v_a_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_quotContext_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_quotContext_4411_ = leanh::lean_ctor_get(v_a_4409_, 1);
    v_currMacroScope_4412_ = leanh::lean_ctor_get(v_a_4409_, 2);
    v_ref_4413_ = leanh::lean_ctor_get(v_a_4409_, 5);
    v___x_4414_ = 0;
    v___x_4415_ = l_Lean_SourceInfo_fromRef(v_ref_4413_, v___x_4414_);
    v___x_4416_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1;
    v___x_4417_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
    v___x_4418_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9;
    v___x_4419_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11;
    v___x_4420_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
    leanh::lean_inc_n(v___x_4415_, 8);
    v___x_4421_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4421_, 0, v___x_4415_);
    leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
    v___x_4422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once), _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
    v___x_4423_ = l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_;
    leanh::lean_inc_n(v_currMacroScope_4412_, 2);
    leanh::lean_inc_n(v_quotContext_4411_, 2);
    v___x_4424_ = l_Lean_addMacroScope(v_quotContext_4411_, v___x_4423_, v_currMacroScope_4412_);
    v___x_4425_ = leanh::lean_box(0);
    v___x_4426_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4426_, 0, v___x_4415_);
    leanh::lean_ctor_set(v___x_4426_, 1, v___x_4422_);
    leanh::lean_ctor_set(v___x_4426_, 2, v___x_4424_);
    leanh::lean_ctor_set(v___x_4426_, 3, v___x_4425_);
    v___x_4427_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
    v___x_4428_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4428_, 0, v___x_4415_);
    leanh::lean_ctor_set(v___x_4428_, 1, v___x_4427_);
    v___x_4429_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
    v___x_4430_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78;
    v___x_4431_ = l_Lean_addMacroScope(v_quotContext_4411_, v___x_4430_, v_currMacroScope_4412_);
    v___x_4432_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82;
    v___x_4433_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4433_, 0, v___x_4415_);
    leanh::lean_ctor_set(v___x_4433_, 1, v___x_4429_);
    leanh::lean_ctor_set(v___x_4433_, 2, v___x_4431_);
    leanh::lean_ctor_set(v___x_4433_, 3, v___x_4432_);
    v___x_4434_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
    v___x_4435_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4435_, 0, v___x_4415_);
    leanh::lean_ctor_set(v___x_4435_, 1, v___x_4434_);
    v___x_4436_ = l_Lean_Syntax_node5(
        v___x_4415_,
        v___x_4419_,
        v___x_4421_,
        v___x_4426_,
        v___x_4428_,
        v___x_4433_,
        v___x_4435_,
    );
    v___x_4437_ = l_Lean_Syntax_node1(v___x_4415_, v___x_4418_, v___x_4436_);
    v___x_4438_ = l_Lean_Syntax_node1(v___x_4415_, v___x_4417_, v___x_4437_);
    v___x_4439_ = l_Lean_Syntax_node1(v___x_4415_, v___x_4416_, v___x_4438_);
    v___x_4440_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__65;
    v___x_4441_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__68;
    v___x_4442_ = l_Lean_Syntax_setKind(v_s_4408_, v___x_4441_);
    v___x_4443_ = leanh::lean_unsigned_to_nat(0);
    v___x_4444_ = l_Lean_Syntax_getArg(v___x_4442_, v___x_4443_);
    v___x_4445_ = 1;
    v___x_4446_ = l_Lean_mkAtomFrom(v___x_4444_, v___x_4440_, v___x_4445_);
    leanh::lean_dec(v___x_4444_);
    v___x_4447_ = l_Lean_Syntax_setArg(v___x_4442_, v___x_4443_, v___x_4446_);
    v___x_4448_ = leanh::lean_unsigned_to_nat(1);
    v___x_4449_ = l_Lean_Syntax_getArg(v___x_4447_, v___x_4448_);
    v___x_4450_ = l_Lean_Parser_Tactic_appendConfig(v___x_4449_, v___x_4439_);
    v___x_4451_ = l_Lean_Syntax_setArg(v___x_4447_, v___x_4448_, v___x_4450_);
    v___x_4452_ = l_Lean_Syntax_mkSynthetic(v___x_4451_);
    v___x_4453_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4453_, 0, v___x_4452_);
    leanh::lean_ctor_set(v___x_4453_, 1, v_a_4410_);
    return v___x_4453_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3____boxed(
    mut v_s_4454_: *mut leanh::LeanObject,
    mut v_a_4455_: *mut leanh::LeanObject,
    mut v_a_4456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_(
        v_s_4454_, v_a_4455_, v_a_4456_,
    );
    leanh::lean_dec_ref(v_a_4455_);
    return v_res_4457_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4469_ = l_Lean_Parser_Tactic_simpArith___closed__3;
    v___x_4470_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4471_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4471_, 0, v___x_4470_);
    leanh::lean_ctor_set(v___x_4471_, 1, v___x_4469_);
    leanh::lean_ctor_set(v___x_4471_, 2, v___x_4468_);
    return v___x_4471_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4473_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__4,
    );
    v___x_4474_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4475_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4475_, 0, v___x_4474_);
    leanh::lean_ctor_set(v___x_4475_, 1, v___x_4473_);
    leanh::lean_ctor_set(v___x_4475_, 2, v___x_4472_);
    return v___x_4475_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4476_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4477_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__5,
    );
    v___x_4478_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4479_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
    leanh::lean_ctor_set(v___x_4479_, 1, v___x_4477_);
    leanh::lean_ctor_set(v___x_4479_, 2, v___x_4476_);
    return v___x_4479_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22,
    );
    v___x_4481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__6,
    );
    v___x_4482_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4483_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4483_, 0, v___x_4482_);
    leanh::lean_ctor_set(v___x_4483_, 1, v___x_4481_);
    leanh::lean_ctor_set(v___x_4483_, 2, v___x_4480_);
    return v___x_4483_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9,
    );
    v___x_4485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__7_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__7,
    );
    v___x_4486_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4487_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4487_, 0, v___x_4486_);
    leanh::lean_ctor_set(v___x_4487_, 1, v___x_4485_);
    leanh::lean_ctor_set(v___x_4487_, 2, v___x_4484_);
    return v___x_4487_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__8_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__8,
    );
    v___x_4489_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4490_ = l_Lean_Parser_Tactic_simpArith___closed__1;
    v___x_4491_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4491_, 0, v___x_4490_);
    leanh::lean_ctor_set(v___x_4491_, 1, v___x_4489_);
    leanh::lean_ctor_set(v___x_4491_, 2, v___x_4488_);
    return v___x_4491_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArith() -> *mut leanh::LeanObject {
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArith___closed__9_once),
        _init_l_Lean_Parser_Tactic_simpArith___closed__9,
    );
    return v___x_4492_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4503_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4504_ = l_Lean_Parser_Tactic_simpArithBang___closed__3;
    v___x_4505_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4506_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4506_, 0, v___x_4505_);
    leanh::lean_ctor_set(v___x_4506_, 1, v___x_4504_);
    leanh::lean_ctor_set(v___x_4506_, 2, v___x_4503_);
    return v___x_4506_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__4,
    );
    v___x_4509_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4510_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4510_, 0, v___x_4509_);
    leanh::lean_ctor_set(v___x_4510_, 1, v___x_4508_);
    leanh::lean_ctor_set(v___x_4510_, 2, v___x_4507_);
    return v___x_4510_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4511_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4512_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__5,
    );
    v___x_4513_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4514_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4514_, 0, v___x_4513_);
    leanh::lean_ctor_set(v___x_4514_, 1, v___x_4512_);
    leanh::lean_ctor_set(v___x_4514_, 2, v___x_4511_);
    return v___x_4514_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__22_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__22,
    );
    v___x_4516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__6,
    );
    v___x_4517_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4518_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4518_, 0, v___x_4517_);
    leanh::lean_ctor_set(v___x_4518_, 1, v___x_4516_);
    leanh::lean_ctor_set(v___x_4518_, 2, v___x_4515_);
    return v___x_4518_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9,
    );
    v___x_4520_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__7_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__7,
    );
    v___x_4521_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4522_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4522_, 0, v___x_4521_);
    leanh::lean_ctor_set(v___x_4522_, 1, v___x_4520_);
    leanh::lean_ctor_set(v___x_4522_, 2, v___x_4519_);
    return v___x_4522_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__8_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__8,
    );
    v___x_4524_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4525_ = l_Lean_Parser_Tactic_simpArithBang___closed__1;
    v___x_4526_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4525_);
    leanh::lean_ctor_set(v___x_4526_, 1, v___x_4524_);
    leanh::lean_ctor_set(v___x_4526_, 2, v___x_4523_);
    return v___x_4526_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpArithBang() -> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpArithBang___closed__9_once),
        _init_l_Lean_Parser_Tactic_simpArithBang___closed__9,
    );
    return v___x_4527_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4538_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4539_ = l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__3;
    v___x_4540_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4541_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4541_, 0, v___x_4540_);
    leanh::lean_ctor_set(v___x_4541_, 1, v___x_4539_);
    leanh::lean_ctor_set(v___x_4541_, 2, v___x_4538_);
    return v___x_4541_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4543_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__4,
    );
    v___x_4544_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4545_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4545_, 0, v___x_4544_);
    leanh::lean_ctor_set(v___x_4545_, 1, v___x_4543_);
    leanh::lean_ctor_set(v___x_4545_, 2, v___x_4542_);
    return v___x_4545_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4547_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__5,
    );
    v___x_4548_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4549_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4549_, 0, v___x_4548_);
    leanh::lean_ctor_set(v___x_4549_, 1, v___x_4547_);
    leanh::lean_ctor_set(v___x_4549_, 2, v___x_4546_);
    return v___x_4549_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = 0;
    v___x_4551_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__17;
    v___x_4552_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__15;
    v___x_4553_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__13_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__13,
    );
    v___x_4554_ = leanh::lean_alloc_ctor(10, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_4554_, 0, v___x_4553_);
    leanh::lean_ctor_set(v___x_4554_, 1, v___x_4552_);
    leanh::lean_ctor_set(v___x_4554_, 2, v___x_4551_);
    leanh::lean_ctor_set_uint8(
        v___x_4554_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4550_,
    );
    return v___x_4554_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4555_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__7,
    );
    v___x_4556_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__12;
    v___x_4557_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4558_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4558_, 0, v___x_4557_);
    leanh::lean_ctor_set(v___x_4558_, 1, v___x_4556_);
    leanh::lean_ctor_set(v___x_4558_, 2, v___x_4555_);
    return v___x_4558_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__20;
    v___x_4560_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__8,
    );
    v___x_4561_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4562_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4562_, 0, v___x_4561_);
    leanh::lean_ctor_set(v___x_4562_, 1, v___x_4560_);
    leanh::lean_ctor_set(v___x_4562_, 2, v___x_4559_);
    return v___x_4562_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4563_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__9,
    );
    v___x_4564_ = l_Lean_Parser_Tactic_tacticErw_______00__closed__8;
    v___x_4565_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4565_, 0, v___x_4564_);
    leanh::lean_ctor_set(v___x_4565_, 1, v___x_4563_);
    return v___x_4565_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4566_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10,
    );
    v___x_4567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__6,
    );
    v___x_4568_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4569_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4569_, 0, v___x_4568_);
    leanh::lean_ctor_set(v___x_4569_, 1, v___x_4567_);
    leanh::lean_ctor_set(v___x_4569_, 2, v___x_4566_);
    return v___x_4569_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__11,
    );
    v___x_4571_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4572_ = l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__1;
    v___x_4573_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4573_, 0, v___x_4572_);
    leanh::lean_ctor_set(v___x_4573_, 1, v___x_4571_);
    leanh::lean_ctor_set(v___x_4573_, 2, v___x_4570_);
    return v___x_4573_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllAutoUnfold() -> *mut leanh::LeanObject {
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4574_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__12,
    );
    return v___x_4574_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(
    mut v_s_4576_: *mut leanh::LeanObject,
    mut v_a_4577_: *mut leanh::LeanObject,
    mut v_a_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_quotContext_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_quotContext_4579_ = leanh::lean_ctor_get(v_a_4577_, 1);
    v_currMacroScope_4580_ = leanh::lean_ctor_get(v_a_4577_, 2);
    v_ref_4581_ = leanh::lean_ctor_get(v_a_4577_, 5);
    v___x_4582_ = 0;
    v___x_4583_ = l_Lean_SourceInfo_fromRef(v_ref_4581_, v___x_4582_);
    v___x_4584_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1;
    v___x_4585_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
    v___x_4586_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9;
    v___x_4587_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11;
    v___x_4588_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
    leanh::lean_inc_n(v___x_4583_, 8);
    v___x_4589_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4589_, 0, v___x_4583_);
    leanh::lean_ctor_set(v___x_4589_, 1, v___x_4588_);
    v___x_4590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once), _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
    v___x_4591_ = l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_;
    leanh::lean_inc_n(v_currMacroScope_4580_, 2);
    leanh::lean_inc_n(v_quotContext_4579_, 2);
    v___x_4592_ = l_Lean_addMacroScope(v_quotContext_4579_, v___x_4591_, v_currMacroScope_4580_);
    v___x_4593_ = leanh::lean_box(0);
    v___x_4594_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4594_, 0, v___x_4583_);
    leanh::lean_ctor_set(v___x_4594_, 1, v___x_4590_);
    leanh::lean_ctor_set(v___x_4594_, 2, v___x_4592_);
    leanh::lean_ctor_set(v___x_4594_, 3, v___x_4593_);
    v___x_4595_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
    v___x_4596_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4596_, 0, v___x_4583_);
    leanh::lean_ctor_set(v___x_4596_, 1, v___x_4595_);
    v___x_4597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
    v___x_4598_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78;
    v___x_4599_ = l_Lean_addMacroScope(v_quotContext_4579_, v___x_4598_, v_currMacroScope_4580_);
    v___x_4600_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82;
    v___x_4601_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4601_, 0, v___x_4583_);
    leanh::lean_ctor_set(v___x_4601_, 1, v___x_4597_);
    leanh::lean_ctor_set(v___x_4601_, 2, v___x_4599_);
    leanh::lean_ctor_set(v___x_4601_, 3, v___x_4600_);
    v___x_4602_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
    v___x_4603_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4603_, 0, v___x_4583_);
    leanh::lean_ctor_set(v___x_4603_, 1, v___x_4602_);
    v___x_4604_ = l_Lean_Syntax_node5(
        v___x_4583_,
        v___x_4587_,
        v___x_4589_,
        v___x_4594_,
        v___x_4596_,
        v___x_4601_,
        v___x_4603_,
    );
    v___x_4605_ = l_Lean_Syntax_node1(v___x_4583_, v___x_4586_, v___x_4604_);
    v___x_4606_ = l_Lean_Syntax_node1(v___x_4583_, v___x_4585_, v___x_4605_);
    v___x_4607_ = l_Lean_Syntax_node1(v___x_4583_, v___x_4584_, v___x_4606_);
    v___x_4608_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__61;
    v___x_4609_ = l_Lean_Syntax_setKind(v_s_4576_, v___x_4608_);
    v___x_4610_ = leanh::lean_unsigned_to_nat(0);
    v___x_4611_ = l_Lean_Syntax_getArg(v___x_4609_, v___x_4610_);
    v___x_4612_ = l_Lean_Parser_Tactic_expandSimp___closed__0_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_;
    v___x_4613_ = 1;
    v___x_4614_ = l_Lean_mkAtomFrom(v___x_4611_, v___x_4612_, v___x_4613_);
    leanh::lean_dec(v___x_4611_);
    v___x_4615_ = l_Lean_Syntax_setArg(v___x_4609_, v___x_4610_, v___x_4614_);
    v___x_4616_ = leanh::lean_unsigned_to_nat(1);
    v___x_4617_ = l_Lean_Syntax_getArg(v___x_4615_, v___x_4616_);
    v___x_4618_ = l_Lean_Parser_Tactic_appendConfig(v___x_4617_, v___x_4607_);
    v___x_4619_ = l_Lean_Syntax_setArg(v___x_4615_, v___x_4616_, v___x_4618_);
    v___x_4620_ = l_Lean_Syntax_mkSynthetic(v___x_4619_);
    v___x_4621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4621_, 0, v___x_4620_);
    leanh::lean_ctor_set(v___x_4621_, 1, v_a_4578_);
    return v___x_4621_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3____boxed(
    mut v_s_4622_: *mut leanh::LeanObject,
    mut v_a_4623_: *mut leanh::LeanObject,
    mut v_a_4624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4625_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_3079349156____hygCtx___hyg_3_(
        v_s_4622_, v_a_4623_, v_a_4624_,
    );
    leanh::lean_dec_ref(v_a_4623_);
    return v_res_4625_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4637_ = l_Lean_Parser_Tactic_simpAllArith___closed__3;
    v___x_4638_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4639_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    leanh::lean_ctor_set(v___x_4639_, 1, v___x_4637_);
    leanh::lean_ctor_set(v___x_4639_, 2, v___x_4636_);
    return v___x_4639_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4641_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpAllArith___closed__4,
    );
    v___x_4642_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4643_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    leanh::lean_ctor_set(v___x_4643_, 1, v___x_4641_);
    leanh::lean_ctor_set(v___x_4643_, 2, v___x_4640_);
    return v___x_4643_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4645_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAllArith___closed__5,
    );
    v___x_4646_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4647_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4647_, 0, v___x_4646_);
    leanh::lean_ctor_set(v___x_4647_, 1, v___x_4645_);
    leanh::lean_ctor_set(v___x_4647_, 2, v___x_4644_);
    return v___x_4647_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10,
    );
    v___x_4649_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpAllArith___closed__6,
    );
    v___x_4650_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4651_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4651_, 0, v___x_4650_);
    leanh::lean_ctor_set(v___x_4651_, 1, v___x_4649_);
    leanh::lean_ctor_set(v___x_4651_, 2, v___x_4648_);
    return v___x_4651_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4652_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__7_once),
        _init_l_Lean_Parser_Tactic_simpAllArith___closed__7,
    );
    v___x_4653_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4654_ = l_Lean_Parser_Tactic_simpAllArith___closed__1;
    v___x_4655_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4655_, 0, v___x_4654_);
    leanh::lean_ctor_set(v___x_4655_, 1, v___x_4653_);
    leanh::lean_ctor_set(v___x_4655_, 2, v___x_4652_);
    return v___x_4655_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArith() -> *mut leanh::LeanObject {
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4656_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArith___closed__8_once),
        _init_l_Lean_Parser_Tactic_simpAllArith___closed__8,
    );
    return v___x_4656_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4668_ = l_Lean_Parser_Tactic_simpAllArithBang___closed__3;
    v___x_4669_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4670_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4670_, 0, v___x_4669_);
    leanh::lean_ctor_set(v___x_4670_, 1, v___x_4668_);
    leanh::lean_ctor_set(v___x_4670_, 2, v___x_4667_);
    return v___x_4670_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4672_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__4_once),
        _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__4,
    );
    v___x_4673_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4674_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4674_, 0, v___x_4673_);
    leanh::lean_ctor_set(v___x_4674_, 1, v___x_4672_);
    leanh::lean_ctor_set(v___x_4674_, 2, v___x_4671_);
    return v___x_4674_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4675_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4676_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__5,
    );
    v___x_4677_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4678_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4678_, 0, v___x_4677_);
    leanh::lean_ctor_set(v___x_4678_, 1, v___x_4676_);
    leanh::lean_ctor_set(v___x_4678_, 2, v___x_4675_);
    return v___x_4678_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10,
    );
    v___x_4680_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__6_once),
        _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__6,
    );
    v___x_4681_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4682_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4682_, 0, v___x_4681_);
    leanh::lean_ctor_set(v___x_4682_, 1, v___x_4680_);
    leanh::lean_ctor_set(v___x_4682_, 2, v___x_4679_);
    return v___x_4682_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4683_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__7_once),
        _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__7,
    );
    v___x_4684_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4685_ = l_Lean_Parser_Tactic_simpAllArithBang___closed__1;
    v___x_4686_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4686_, 0, v___x_4685_);
    leanh::lean_ctor_set(v___x_4686_, 1, v___x_4684_);
    leanh::lean_ctor_set(v___x_4686_, 2, v___x_4683_);
    return v___x_4686_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_simpAllArithBang() -> *mut leanh::LeanObject {
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllArithBang___closed__8_once),
        _init_l_Lean_Parser_Tactic_simpAllArithBang___closed__8,
    );
    return v___x_4687_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4699_ = l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__3;
    v___x_4700_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4701_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4701_, 0, v___x_4700_);
    leanh::lean_ctor_set(v___x_4701_, 1, v___x_4699_);
    leanh::lean_ctor_set(v___x_4701_, 2, v___x_4698_);
    return v___x_4701_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4702_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_simpAutoUnfold___closed__5,
    );
    v___x_4703_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__4,
    );
    v___x_4704_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4705_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4705_, 0, v___x_4704_);
    leanh::lean_ctor_set(v___x_4705_, 1, v___x_4703_);
    leanh::lean_ctor_set(v___x_4705_, 2, v___x_4702_);
    return v___x_4705_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4706_ = l_Lean_Parser_Tactic_simpAutoUnfold___closed__9;
    v___x_4707_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__5,
    );
    v___x_4708_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4709_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4709_, 0, v___x_4708_);
    leanh::lean_ctor_set(v___x_4709_, 1, v___x_4707_);
    leanh::lean_ctor_set(v___x_4709_, 2, v___x_4706_);
    return v___x_4709_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10_once),
        _init_l_Lean_Parser_Tactic_simpAllAutoUnfold___closed__10,
    );
    v___x_4711_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__6,
    );
    v___x_4712_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4713_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4713_, 0, v___x_4712_);
    leanh::lean_ctor_set(v___x_4713_, 1, v___x_4711_);
    leanh::lean_ctor_set(v___x_4713_, 2, v___x_4710_);
    return v___x_4713_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4714_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_tacticErw_______00__closed__9_once),
        _init_l_Lean_Parser_Tactic_tacticErw_______00__closed__9,
    );
    v___x_4715_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__7,
    );
    v___x_4716_ = l_Lean_termEval__prec___00__closed__3;
    v___x_4717_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4717_, 0, v___x_4716_);
    leanh::lean_ctor_set(v___x_4717_, 1, v___x_4715_);
    leanh::lean_ctor_set(v___x_4717_, 2, v___x_4714_);
    return v___x_4717_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__8,
    );
    v___x_4719_ = leanh::lean_unsigned_to_nat(1022);
    v___x_4720_ = l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__1;
    v___x_4721_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4721_, 0, v___x_4720_);
    leanh::lean_ctor_set(v___x_4721_, 1, v___x_4719_);
    leanh::lean_ctor_set(v___x_4721_, 2, v___x_4718_);
    return v___x_4721_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_dsimpAutoUnfold() -> *mut leanh::LeanObject {
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4722_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9_once),
        _init_l_Lean_Parser_Tactic_dsimpAutoUnfold___closed__9,
    );
    return v___x_4722_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(
    mut v_s_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
    mut v_a_4725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_quotContext_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: u8 = 0;
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_quotContext_4726_ = leanh::lean_ctor_get(v_a_4724_, 1);
    v_currMacroScope_4727_ = leanh::lean_ctor_get(v_a_4724_, 2);
    v_ref_4728_ = leanh::lean_ctor_get(v_a_4724_, 5);
    v___x_4729_ = 0;
    v___x_4730_ = l_Lean_SourceInfo_fromRef(v_ref_4728_, v___x_4729_);
    v___x_4731_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__1;
    v___x_4732_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__6;
    v___x_4733_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__9;
    v___x_4734_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__11;
    v___x_4735_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__12;
    leanh::lean_inc_n(v___x_4730_, 8);
    v___x_4736_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4736_, 0, v___x_4730_);
    leanh::lean_ctor_set(v___x_4736_, 1, v___x_4735_);
    v___x_4737_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3__once), _init_l_Lean_Parser_Tactic_expandSimp___closed__1_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_);
    v___x_4738_ = l_Lean_Parser_Tactic_expandSimp___closed__2_00___x40_Init_Meta_4021577198____hygCtx___hyg_3_;
    leanh::lean_inc_n(v_currMacroScope_4727_, 2);
    leanh::lean_inc_n(v_quotContext_4726_, 2);
    v___x_4739_ = l_Lean_addMacroScope(v_quotContext_4726_, v___x_4738_, v_currMacroScope_4727_);
    v___x_4740_ = leanh::lean_box(0);
    v___x_4741_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4741_, 0, v___x_4730_);
    leanh::lean_ctor_set(v___x_4741_, 1, v___x_4737_);
    leanh::lean_ctor_set(v___x_4741_, 2, v___x_4739_);
    leanh::lean_ctor_set(v___x_4741_, 3, v___x_4740_);
    v___x_4742_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__16;
    v___x_4743_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4743_, 0, v___x_4730_);
    leanh::lean_ctor_set(v___x_4743_, 1, v___x_4742_);
    v___x_4744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77_once), _init_l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__77);
    v___x_4745_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__78;
    v___x_4746_ = l_Lean_addMacroScope(v_quotContext_4726_, v___x_4745_, v_currMacroScope_4727_);
    v___x_4747_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___lam__2___closed__82;
    v___x_4748_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4748_, 0, v___x_4730_);
    leanh::lean_ctor_set(v___x_4748_, 1, v___x_4744_);
    leanh::lean_ctor_set(v___x_4748_, 2, v___x_4746_);
    leanh::lean_ctor_set(v___x_4748_, 3, v___x_4747_);
    v___x_4749_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1___closed__30;
    v___x_4750_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4750_, 0, v___x_4730_);
    leanh::lean_ctor_set(v___x_4750_, 1, v___x_4749_);
    v___x_4751_ = l_Lean_Syntax_node5(
        v___x_4730_,
        v___x_4734_,
        v___x_4736_,
        v___x_4741_,
        v___x_4743_,
        v___x_4748_,
        v___x_4750_,
    );
    v___x_4752_ = l_Lean_Syntax_node1(v___x_4730_, v___x_4733_, v___x_4751_);
    v___x_4753_ = l_Lean_Syntax_node1(v___x_4730_, v___x_4732_, v___x_4752_);
    v___x_4754_ = l_Lean_Syntax_node1(v___x_4730_, v___x_4731_, v___x_4753_);
    v___x_4755_ = l_Lean_Parser_Tactic_dsimpKind___closed__2;
    v___x_4756_ = l_Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__declareSimpLikeTactic__1___closed__52;
    v___x_4757_ = l_Lean_Syntax_setKind(v_s_4723_, v___x_4756_);
    v___x_4758_ = leanh::lean_unsigned_to_nat(0);
    v___x_4759_ = l_Lean_Syntax_getArg(v___x_4757_, v___x_4758_);
    v___x_4760_ = 1;
    v___x_4761_ = l_Lean_mkAtomFrom(v___x_4759_, v___x_4755_, v___x_4760_);
    leanh::lean_dec(v___x_4759_);
    v___x_4762_ = l_Lean_Syntax_setArg(v___x_4757_, v___x_4758_, v___x_4761_);
    v___x_4763_ = leanh::lean_unsigned_to_nat(1);
    v___x_4764_ = l_Lean_Syntax_getArg(v___x_4762_, v___x_4763_);
    v___x_4765_ = l_Lean_Parser_Tactic_appendConfig(v___x_4764_, v___x_4754_);
    v___x_4766_ = l_Lean_Syntax_setArg(v___x_4762_, v___x_4763_, v___x_4765_);
    v___x_4767_ = l_Lean_Syntax_mkSynthetic(v___x_4766_);
    v___x_4768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4768_, 0, v___x_4767_);
    leanh::lean_ctor_set(v___x_4768_, 1, v_a_4725_);
    return v___x_4768_;
}
pub unsafe fn l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3____boxed(
    mut v_s_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4772_ = l_Lean_Parser_Tactic_expandSimp_00___x40_Init_Meta_4207919134____hygCtx___hyg_3_(
        v_s_4769_, v_a_4770_, v_a_4771_,
    );
    leanh::lean_dec_ref(v_a_4770_);
    return v_res_4772_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Meta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Meta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_Tactic_tacticErw______ = _init_l_Lean_Parser_Tactic_tacticErw______();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_tacticErw______);
    l_Lean_Parser_Tactic_declareSimpLikeTactic = _init_l_Lean_Parser_Tactic_declareSimpLikeTactic();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_declareSimpLikeTactic);
    l_Lean_Parser_Tactic_simpAutoUnfold = _init_l_Lean_Parser_Tactic_simpAutoUnfold();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpAutoUnfold);
    l_Lean_Parser_Tactic_simpArith = _init_l_Lean_Parser_Tactic_simpArith();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpArith);
    l_Lean_Parser_Tactic_simpArithBang = _init_l_Lean_Parser_Tactic_simpArithBang();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpArithBang);
    l_Lean_Parser_Tactic_simpAllAutoUnfold = _init_l_Lean_Parser_Tactic_simpAllAutoUnfold();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpAllAutoUnfold);
    l_Lean_Parser_Tactic_simpAllArith = _init_l_Lean_Parser_Tactic_simpAllArith();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpAllArith);
    l_Lean_Parser_Tactic_simpAllArithBang = _init_l_Lean_Parser_Tactic_simpAllArithBang();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_simpAllArithBang);
    l_Lean_Parser_Tactic_dsimpAutoUnfold = _init_l_Lean_Parser_Tactic_dsimpAutoUnfold();
    leanh::lean_mark_persistent(l_Lean_Parser_Tactic_dsimpAutoUnfold);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Meta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Meta(builtin);
}
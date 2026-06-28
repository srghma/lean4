// Lean compiler output
// Module: Std.Do.PostCond
// Imports: Std.Do.SPred
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Do::SPred::SPred::{
    l_Std_Do_SPred_and, l_Std_Do_SPred_imp, l_Std_Do_SPred_pure___redArg,
};
use crate::r#gen::Std::Do::SPred::SVal::l_Std_Do_SVal_curry___redArg;
use crate::r#gen::Std::Do::SPred::{initialize_Std_Do_SPred, runtime_initialize_Std_Do_SPred};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Std_Do_term___u22a2_u2091___00__closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__1_value: LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__2_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 138, 162, 226, 130, 145, 95, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__2_value) as *mut LeanObject;
static l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u22a2_u2091___00__closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__2_value) as *mut LeanObject,
        6035889643370630703 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__4_value: LeanStringObject<8> =
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
static mut l_Std_Do_term___u22a2_u2091___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__4_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__6_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 138, 162, 226, 130, 145, 32, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__6_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__7_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__8_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__8_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__8_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value) as *mut LeanObject,
        (((25 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__11_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__12_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value) as *mut LeanObject,
        (((25 as usize) << 1) | 1) as *mut LeanObject,
        (((26 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u2091___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__12_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u22a2_u2091__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__12_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17055763123476927371 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut LeanObject,13614334605615213219 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17808102113152393460 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut LeanObject,7198879216713715016 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 136, 167, 226, 130, 145, 95, 0],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u2227_u2091___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__0_value) as *mut LeanObject,
        11687468331848102906 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u2091___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 136, 167, 226, 130, 145, 32, 0],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u2091___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u2091___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u2091___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__6_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        (((36 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u2091___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__6_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u2227_u2091__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__6_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17055763123476927371 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut LeanObject,14567852056292133 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17808102113152393460 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut LeanObject,8609142911669095622 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 134, 146, 226, 130, 145, 95, 0],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u2192_u2091___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__0_value) as *mut LeanObject,
        4432936103724110417 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u2091___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 134, 146, 226, 130, 145, 32, 0],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u2091___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u2091___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value) as *mut LeanObject,
        (((25 as usize) << 1) | 1) as *mut LeanObject,
        (((26 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u2091___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__5_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u2192_u2091__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17055763123476927371 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut LeanObject,4282481912481944283 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut LeanObject,17808102113152393460 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut LeanObject,6967440820911327760 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 13,
        m_data: [
            116, 101, 114, 109, 80, 111, 115, 116, 226, 159, 168, 95, 44, 44, 226, 159, 169, 0,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value)
        as *mut LeanObject;
static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value)
                as *mut LeanObject,
            17707010111776501109 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 5,
        m_data: [112, 111, 115, 116, 226, 159, 168, 0],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value: LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value: LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value)
                as *mut LeanObject,
            1 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 169, 0],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value)
        as *mut LeanObject;
pub static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value) as *mut LeanObject,16173796135615239867 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value) as *mut LeanObject,14997215300048349804 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 85, 110, 105, 116, 46, 117, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 85, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value) as *mut LeanObject,11091137386503903511 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value) as *mut LeanObject,14036392901208071058 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 10,
        m_data: [116, 101, 114, 109, 95, 226, 135, 147, 95, 61, 62, 95, 0],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value)
                as *mut LeanObject,
            8463861479368259073 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value: LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value)
                as *mut LeanObject,
            2214559063752339918 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value: LeanStringObject<17> =
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
            112, 112, 65, 108, 108, 111, 119, 85, 110, 103, 114, 111, 117, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value)
                as *mut LeanObject,
            211807283801307390 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 135, 147, 0],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value: LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value)
                as *mut LeanObject,
            17243740965612849207 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value: LeanStringObject<5> =
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
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u21d3___x3d_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 110, 111, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut LeanObject,3676176009791887579 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut LeanObject,11553573755926099728 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16: *mut LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value) as *mut LeanObject,13979102795498516556 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 114, 101, 100, 40, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value) as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 11,
        m_data: [116, 101, 114, 109, 95, 226, 135, 147, 63, 95, 61, 62, 95, 0],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value)
        as *mut LeanObject;
static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value)
                as *mut LeanObject,
            5101830612129297492 as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [226, 135, 147, 63, 0],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value)
        as *mut LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value)
        as *mut LeanObject;
pub static mut l_Std_Do_term___u21d3_x3f___x3d_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value)
        as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut LeanObject,7425120582457359416 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut LeanObject,2940964116523157683 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 138, 162, 226, 130, 154, 95, 0],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u22a2_u209a___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__0_value) as *mut LeanObject,
        597832130936671675 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u209a___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 138, 162, 226, 130, 154, 32, 0],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u209a___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u209a___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value) as *mut LeanObject,
        (((25 as usize) << 1) | 1) as *mut LeanObject,
        (((26 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u22a2_u209a___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__5_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u22a2_u209a__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1: *mut LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut LeanObject,16792813948254738635 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut LeanObject,717208579114757920 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 136, 167, 226, 130, 154, 95, 0],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u2227_u209a___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__0_value) as *mut LeanObject,
        15844678083483941974 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u209a___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 136, 167, 226, 130, 154, 32, 0],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u209a___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u209a___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value) as *mut LeanObject,
        (((35 as usize) << 1) | 1) as *mut LeanObject,
        (((36 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2227_u209a___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__5_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u2227_u209a__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1: *mut LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut LeanObject,15623922605380786509 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut LeanObject,9858637187560378014 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 8,
        m_data: [116, 101, 114, 109, 95, 226, 134, 146, 226, 130, 154, 95, 0],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__0_value) as *mut LeanObject;
static l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Std_Do_term___u2192_u209a___00__closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__0_value) as *mut LeanObject,
        2942702865894185004 as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u209a___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 4,
        m_data: [32, 226, 134, 146, 226, 130, 154, 32, 0],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__2_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u209a___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__3_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u209a___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__4_value) as *mut LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__5_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value) as *mut LeanObject,
        (((25 as usize) << 1) | 1) as *mut LeanObject,
        (((26 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Do_term___u2192_u209a___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__5_value) as *mut LeanObject;
pub static mut l_Std_Do_term___u2192_u209a__: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__5_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value) as *mut LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1: *mut LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut LeanObject,6564238721344519347 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value) as *mut LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut LeanObject,11225800798110998584 as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value) as *mut LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value) as *mut LeanObject;
pub unsafe fn l_Std_Do_PostShape_ctorIdx(mut v_x_1425_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1425_) {
        0 => {
            let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
            v___x_1426_ = lean_unsigned_to_nat(0);
            return v___x_1426_;
        }
        1 => {
            let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
            v___x_1427_ = lean_unsigned_to_nat(1);
            return v___x_1427_;
        }
        _ => {
            let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
            v___x_1428_ = lean_unsigned_to_nat(2);
            return v___x_1428_;
        }
    }
}
pub unsafe fn l_Std_Do_PostShape_ctorIdx___boxed(
    mut v_x_1429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1430_: *mut LeanObject = core::ptr::null_mut();
    v_res_1430_ = l_Std_Do_PostShape_ctorIdx(v_x_1429_);
    lean_dec(v_x_1429_);
    return v_res_1430_;
}
pub unsafe fn l_Std_Do_PostShape_ctorElim___redArg(
    mut v_t_1431_: *mut LeanObject,
    mut v_k_1432_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1431_) == 0 {
        return v_k_1432_;
    } else {
        let mut v_a_1433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
        v_a_1433_ = lean_ctor_get(v_t_1431_, 0);
        lean_inc(v_a_1433_);
        lean_dec(v_t_1431_);
        v___x_1434_ = lean_apply_2(v_k_1432_, lean_box(0), v_a_1433_);
        return v___x_1434_;
    }
}
pub unsafe fn l_Std_Do_PostShape_ctorElim(
    mut v_motive_1435_: *mut LeanObject,
    mut v_ctorIdx_1436_: *mut LeanObject,
    mut v_t_1437_: *mut LeanObject,
    mut v_h_1438_: *mut LeanObject,
    mut v_k_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1437_, v_k_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_Do_PostShape_ctorElim___boxed(
    mut v_motive_1441_: *mut LeanObject,
    mut v_ctorIdx_1442_: *mut LeanObject,
    mut v_t_1443_: *mut LeanObject,
    mut v_h_1444_: *mut LeanObject,
    mut v_k_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1446_: *mut LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Std_Do_PostShape_ctorElim(
        v_motive_1441_,
        v_ctorIdx_1442_,
        v_t_1443_,
        v_h_1444_,
        v_k_1445_,
    );
    lean_dec(v_ctorIdx_1442_);
    return v_res_1446_;
}
pub unsafe fn l_Std_Do_PostShape_pure_elim___redArg(
    mut v_t_1447_: *mut LeanObject,
    mut v_pure_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    v___x_1449_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1447_, v_pure_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Std_Do_PostShape_pure_elim(
    mut v_motive_1450_: *mut LeanObject,
    mut v_t_1451_: *mut LeanObject,
    mut v_h_1452_: *mut LeanObject,
    mut v_pure_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1451_, v_pure_1453_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Do_PostShape_arg_elim___redArg(
    mut v_t_1455_: *mut LeanObject,
    mut v_arg_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1455_, v_arg_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Std_Do_PostShape_arg_elim(
    mut v_motive_1458_: *mut LeanObject,
    mut v_t_1459_: *mut LeanObject,
    mut v_h_1460_: *mut LeanObject,
    mut v_arg_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1459_, v_arg_1461_);
    return v___x_1462_;
}
pub unsafe fn l_Std_Do_PostShape_except_elim___redArg(
    mut v_t_1463_: *mut LeanObject,
    mut v_except_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1463_, v_except_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Std_Do_PostShape_except_elim(
    mut v_motive_1466_: *mut LeanObject,
    mut v_t_1467_: *mut LeanObject,
    mut v_h_1468_: *mut LeanObject,
    mut v_except_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1470_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1467_, v_except_1469_);
    return v___x_1470_;
}
pub unsafe fn l_Std_Do_PostShape_args(mut v_x_1471_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1471_) {
                0 => {
                    v___x_1472_ = lean_box(0);
                    return v___x_1472_;
                }
                1 => {
                    v_a_1473_ = lean_ctor_get(v_x_1471_, 0);
                    v___x_1474_ = l_Std_Do_PostShape_args(v_a_1473_);
                    v___x_1475_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1475_, 0, lean_box(0));
                    lean_ctor_set(v___x_1475_, 1, v___x_1474_);
                    return v___x_1475_;
                }
                _ => {
                    v_a_1476_ = lean_ctor_get(v_x_1471_, 0);
                    v_x_1471_ = v_a_1476_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PostShape_args___boxed(mut v_x_1478_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1479_: *mut LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Std_Do_PostShape_args(v_x_1478_);
    lean_dec(v_x_1478_);
    return v_res_1479_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg___lam__0(
    mut v_a_1480_: *mut LeanObject,
    mut v_00___u03b5_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    v___x_1482_ = l_Std_Do_PostShape_args(v_a_1480_);
    v___x_1483_ = l_Std_Do_SPred_pure___redArg(v___x_1482_);
    return v___x_1483_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg___lam__0___boxed(
    mut v_a_1484_: *mut LeanObject,
    mut v_00___u03b5_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1486_: *mut LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_Std_Do_ExceptConds_const___redArg___lam__0(v_a_1484_, v_00___u03b5_1485_);
    lean_dec(v_00___u03b5_1485_);
    lean_dec(v_a_1484_);
    return v_res_1486_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg(
    mut v_ps_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_ps_1487_) {
                0 => {
                    v___x_1488_ = lean_box(0);
                    return v___x_1488_;
                }
                1 => {
                    v_a_1489_ = lean_ctor_get(v_ps_1487_, 0);
                    lean_inc(v_a_1489_);
                    lean_dec_ref_known(v_ps_1487_, 1);
                    v_ps_1487_ = v_a_1489_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1491_ = lean_ctor_get(v_ps_1487_, 0);
                    lean_inc_n(v_a_1491_, 2);
                    lean_dec_ref_known(v_ps_1487_, 1);
                    v___f_1492_ = lean_alloc_closure(
                        l_Std_Do_ExceptConds_const___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1492_, 0, v_a_1491_);
                    v___x_1493_ = l_Std_Do_ExceptConds_const___redArg(v_a_1491_);
                    v___x_1494_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1494_, 0, v___f_1492_);
                    lean_ctor_set(v___x_1494_, 1, v___x_1493_);
                    return v___x_1494_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_ExceptConds_const(
    mut v_ps_1495_: *mut LeanObject,
    mut v_p_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1495_);
    return v___x_1497_;
}
pub unsafe fn l_Std_Do_ExceptConds_true(mut v_ps_1498_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1498_);
    return v___x_1499_;
}
pub unsafe fn l_Std_Do_ExceptConds_false(mut v_ps_1500_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1501_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Std_Do_instInhabitedExceptConds(
    mut v_ps_1502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6()
-> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5;
    v___x_1544_ = l_String_toRawSubstring_x27(v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(
    mut v_x_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
    mut v_a_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    v___x_1572_ = l_Std_Do_term___u22a2_u2091___00__closed__3;
    lean_inc(v_x_1569_);
    v___x_1573_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1572_);
    if v___x_1573_ == 0 {
        let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1569_);
        v___x_1574_ = lean_box(1);
        v___x_1575_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1575_, 0, v___x_1574_);
        lean_ctor_set(v___x_1575_, 1, v_a_1571_);
        return v___x_1575_;
    } else {
        let mut v_quotContext_1576_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1577_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: u8 = 0;
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1576_ = lean_ctor_get(v_a_1570_, 1);
        v_currMacroScope_1577_ = lean_ctor_get(v_a_1570_, 2);
        v_ref_1578_ = lean_ctor_get(v_a_1570_, 5);
        v___x_1579_ = lean_unsigned_to_nat(0);
        v___x_1580_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1579_);
        v___x_1581_ = lean_unsigned_to_nat(2);
        v___x_1582_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1581_);
        lean_dec(v_x_1569_);
        v___x_1583_ = 0;
        v___x_1584_ = l_Lean_SourceInfo_fromRef(v_ref_1578_, v___x_1583_);
        v___x_1585_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1586_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6);
        v___x_1587_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9;
        lean_inc(v_currMacroScope_1577_);
        lean_inc(v_quotContext_1576_);
        v___x_1588_ =
            l_Lean_addMacroScope(v_quotContext_1576_, v___x_1587_, v_currMacroScope_1577_);
        v___x_1589_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14;
        lean_inc_n(v___x_1584_, 2);
        v___x_1590_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1590_, 0, v___x_1584_);
        lean_ctor_set(v___x_1590_, 1, v___x_1586_);
        lean_ctor_set(v___x_1590_, 2, v___x_1588_);
        lean_ctor_set(v___x_1590_, 3, v___x_1589_);
        v___x_1591_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1592_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1591_, v___x_1580_, v___x_1582_);
        v___x_1593_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1585_, v___x_1590_, v___x_1592_);
        v___x_1594_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1594_, 0, v___x_1593_);
        lean_ctor_set(v___x_1594_, 1, v_a_1571_);
        return v___x_1594_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___boxed(
    mut v_x_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(
            v_x_1595_, v_a_1596_, v_a_1597_,
        );
    lean_dec_ref(v_a_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(
    mut v_x_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    v___x_1605_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_1602_);
    v___x_1606_ = l_Lean_Syntax_isOfKind(v_x_1602_, v___x_1605_);
    if v___x_1606_ == 0 {
        let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1602_);
        v___x_1607_ = lean_box(0);
        v___x_1608_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1608_, 0, v___x_1607_);
        lean_ctor_set(v___x_1608_, 1, v_a_1604_);
        return v___x_1608_;
    } else {
        let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1612_: u8 = 0;
        v___x_1609_ = lean_unsigned_to_nat(0);
        v___x_1610_ = l_Lean_Syntax_getArg(v_x_1602_, v___x_1609_);
        v___x_1611_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_1610_);
        v___x_1612_ = l_Lean_Syntax_isOfKind(v___x_1610_, v___x_1611_);
        if v___x_1612_ == 0 {
            let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1610_);
            lean_dec(v_x_1602_);
            v___x_1613_ = lean_box(0);
            v___x_1614_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1614_, 0, v___x_1613_);
            lean_ctor_set(v___x_1614_, 1, v_a_1604_);
            return v___x_1614_;
        } else {
            let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: u8 = 0;
            v___x_1615_ = lean_unsigned_to_nat(1);
            v___x_1616_ = l_Lean_Syntax_getArg(v_x_1602_, v___x_1615_);
            lean_dec(v_x_1602_);
            v___x_1617_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1616_);
            v___x_1618_ = l_Lean_Syntax_matchesNull(v___x_1616_, v___x_1617_);
            if v___x_1618_ == 0 {
                let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1616_);
                lean_dec(v___x_1610_);
                v___x_1619_ = lean_box(0);
                v___x_1620_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1620_, 0, v___x_1619_);
                lean_ctor_set(v___x_1620_, 1, v_a_1604_);
                return v___x_1620_;
            } else {
                let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1623_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1624_: u8 = 0;
                let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
                v___x_1621_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1609_);
                v___x_1622_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1615_);
                lean_dec(v___x_1616_);
                v_ref_1623_ = l_Lean_replaceRef(v___x_1610_, v_a_1603_);
                lean_dec(v___x_1610_);
                v___x_1624_ = 0;
                v___x_1625_ = l_Lean_SourceInfo_fromRef(v_ref_1623_, v___x_1624_);
                lean_dec(v_ref_1623_);
                v___x_1626_ = l_Std_Do_term___u22a2_u2091___00__closed__3;
                v___x_1627_ = l_Std_Do_term___u22a2_u2091___00__closed__6;
                lean_inc(v___x_1625_);
                v___x_1628_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1628_, 0, v___x_1625_);
                lean_ctor_set(v___x_1628_, 1, v___x_1627_);
                v___x_1629_ = l_Lean_Syntax_node3(
                    v___x_1625_,
                    v___x_1626_,
                    v___x_1621_,
                    v___x_1628_,
                    v___x_1622_,
                );
                v___x_1630_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1630_, 0, v___x_1629_);
                lean_ctor_set(v___x_1630_, 1, v_a_1604_);
                return v___x_1630_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___boxed(
    mut v_x_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1634_: *mut LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(
        v_x_1631_, v_a_1632_, v_a_1633_,
    );
    lean_dec(v_a_1632_);
    return v_res_1634_;
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(
    mut v_ps_1635_: *mut LeanObject,
    mut v_x_1636_: *mut LeanObject,
    mut v_y_1637_: *mut LeanObject,
    mut v_h__1_1638_: *mut LeanObject,
    mut v_h__2_1639_: *mut LeanObject,
    mut v_h__3_1640_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ps_1635_) {
        0 => {
            let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1640_);
            lean_dec(v_h__2_1639_);
            v___x_1641_ = lean_apply_2(v_h__1_1638_, v_x_1636_, v_y_1637_);
            return v___x_1641_;
        }
        1 => {
            let mut v_a_1642_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1640_);
            lean_dec(v_h__1_1638_);
            v_a_1642_ = lean_ctor_get(v_ps_1635_, 0);
            lean_inc(v_a_1642_);
            lean_dec_ref_known(v_ps_1635_, 1);
            v___x_1643_ = lean_apply_4(v_h__2_1639_, lean_box(0), v_a_1642_, v_x_1636_, v_y_1637_);
            return v___x_1643_;
        }
        _ => {
            let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1639_);
            lean_dec(v_h__1_1638_);
            v_a_1644_ = lean_ctor_get(v_ps_1635_, 0);
            lean_inc(v_a_1644_);
            lean_dec_ref_known(v_ps_1635_, 1);
            v___x_1645_ = lean_apply_4(v_h__3_1640_, lean_box(0), v_a_1644_, v_x_1636_, v_y_1637_);
            return v___x_1645_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter(
    mut v_motive_1646_: *mut LeanObject,
    mut v_ps_1647_: *mut LeanObject,
    mut v_x_1648_: *mut LeanObject,
    mut v_y_1649_: *mut LeanObject,
    mut v_h__1_1650_: *mut LeanObject,
    mut v_h__2_1651_: *mut LeanObject,
    mut v_h__3_1652_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ps_1647_) {
        0 => {
            let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1652_);
            lean_dec(v_h__2_1651_);
            v___x_1653_ = lean_apply_2(v_h__1_1650_, v_x_1648_, v_y_1649_);
            return v___x_1653_;
        }
        1 => {
            let mut v_a_1654_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1652_);
            lean_dec(v_h__1_1650_);
            v_a_1654_ = lean_ctor_get(v_ps_1647_, 0);
            lean_inc(v_a_1654_);
            lean_dec_ref_known(v_ps_1647_, 1);
            v___x_1655_ = lean_apply_4(v_h__2_1651_, lean_box(0), v_a_1654_, v_x_1648_, v_y_1649_);
            return v___x_1655_;
        }
        _ => {
            let mut v_a_1656_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1651_);
            lean_dec(v_h__1_1650_);
            v_a_1656_ = lean_ctor_get(v_ps_1647_, 0);
            lean_inc(v_a_1656_);
            lean_dec_ref_known(v_ps_1647_, 1);
            v___x_1657_ = lean_apply_4(v_h__3_1652_, lean_box(0), v_a_1656_, v_x_1648_, v_y_1649_);
            return v___x_1657_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(
    mut v_x_1658_: *mut LeanObject,
    mut v_h__1_1659_: *mut LeanObject,
    mut v_h__2_1660_: *mut LeanObject,
    mut v_h__3_1661_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1658_) {
        0 => {
            let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1661_);
            lean_dec(v_h__2_1660_);
            v___x_1662_ = lean_box(0);
            v___x_1663_ = lean_apply_1(v_h__1_1659_, v___x_1662_);
            return v___x_1663_;
        }
        1 => {
            let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1661_);
            lean_dec(v_h__1_1659_);
            v_a_1664_ = lean_ctor_get(v_x_1658_, 0);
            lean_inc(v_a_1664_);
            lean_dec_ref_known(v_x_1658_, 1);
            v___x_1665_ = lean_apply_2(v_h__2_1660_, lean_box(0), v_a_1664_);
            return v___x_1665_;
        }
        _ => {
            let mut v_a_1666_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1660_);
            lean_dec(v_h__1_1659_);
            v_a_1666_ = lean_ctor_get(v_x_1658_, 0);
            lean_inc(v_a_1666_);
            lean_dec_ref_known(v_x_1658_, 1);
            v___x_1667_ = lean_apply_2(v_h__3_1661_, lean_box(0), v_a_1666_);
            return v___x_1667_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter(
    mut v_motive_1668_: *mut LeanObject,
    mut v_x_1669_: *mut LeanObject,
    mut v_h__1_1670_: *mut LeanObject,
    mut v_h__2_1671_: *mut LeanObject,
    mut v_h__3_1672_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1669_) {
        0 => {
            let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1672_);
            lean_dec(v_h__2_1671_);
            v___x_1673_ = lean_box(0);
            v___x_1674_ = lean_apply_1(v_h__1_1670_, v___x_1673_);
            return v___x_1674_;
        }
        1 => {
            let mut v_a_1675_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1672_);
            lean_dec(v_h__1_1670_);
            v_a_1675_ = lean_ctor_get(v_x_1669_, 0);
            lean_inc(v_a_1675_);
            lean_dec_ref_known(v_x_1669_, 1);
            v___x_1676_ = lean_apply_2(v_h__2_1671_, lean_box(0), v_a_1675_);
            return v___x_1676_;
        }
        _ => {
            let mut v_a_1677_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1671_);
            lean_dec(v_h__1_1670_);
            v_a_1677_ = lean_ctor_get(v_x_1669_, 0);
            lean_inc(v_a_1677_);
            lean_dec_ref_known(v_x_1669_, 1);
            v___x_1678_ = lean_apply_2(v_h__3_1672_, lean_box(0), v_a_1677_);
            return v___x_1678_;
        }
    }
}
pub unsafe fn l_Std_Do_ExceptConds_and___lam__0(
    mut v_a_1679_: *mut LeanObject,
    mut v_fst_1680_: *mut LeanObject,
    mut v_fst_1681_: *mut LeanObject,
    mut v_e_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_Do_PostShape_args(v_a_1679_);
    lean_inc(v_e_1682_);
    v___x_1684_ = lean_apply_1(v_fst_1680_, v_e_1682_);
    v___x_1685_ = lean_apply_1(v_fst_1681_, v_e_1682_);
    v___x_1686_ = l_Std_Do_SPred_and(v___x_1683_, v___x_1684_, v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Std_Do_ExceptConds_and___lam__0___boxed(
    mut v_a_1687_: *mut LeanObject,
    mut v_fst_1688_: *mut LeanObject,
    mut v_fst_1689_: *mut LeanObject,
    mut v_e_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1691_: *mut LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Std_Do_ExceptConds_and___lam__0(v_a_1687_, v_fst_1688_, v_fst_1689_, v_e_1690_);
    lean_dec(v_a_1687_);
    return v_res_1691_;
}
pub unsafe fn l_Std_Do_ExceptConds_and(
    mut v_ps_1692_: *mut LeanObject,
    mut v_x_1693_: *mut LeanObject,
    mut v_y_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___f_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_ps_1692_) {
                0 => {
                    lean_dec(v_y_1694_);
                    lean_dec(v_x_1693_);
                    v___x_1695_ = lean_box(0);
                    return v___x_1695_;
                }
                1 => {
                    v_a_1696_ = lean_ctor_get(v_ps_1692_, 0);
                    lean_inc(v_a_1696_);
                    lean_dec_ref_known(v_ps_1692_, 1);
                    v_ps_1692_ = v_a_1696_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1698_ = lean_ctor_get(v_ps_1692_, 0);
                    lean_inc(v_a_1698_);
                    lean_dec_ref_known(v_ps_1692_, 1);
                    v_fst_1699_ = lean_ctor_get(v_x_1693_, 0);
                    lean_inc(v_fst_1699_);
                    v_snd_1700_ = lean_ctor_get(v_x_1693_, 1);
                    lean_inc(v_snd_1700_);
                    lean_dec(v_x_1693_);
                    v_fst_1701_ = lean_ctor_get(v_y_1694_, 0);
                    v_snd_1702_ = lean_ctor_get(v_y_1694_, 1);
                    v_isSharedCheck_1711_ = (!lean_is_exclusive(v_y_1694_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1704_ = v_y_1694_;
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1702_);
                        lean_inc(v_fst_1701_);
                        lean_dec(v_y_1694_);
                        v___x_1704_ = lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                lean_inc(v_a_1698_);
                v___f_1706_ = lean_alloc_closure(
                    l_Std_Do_ExceptConds_and___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_1706_, 0, v_a_1698_);
                lean_closure_set(v___f_1706_, 1, v_fst_1699_);
                lean_closure_set(v___f_1706_, 2, v_fst_1701_);
                v___x_1707_ = l_Std_Do_ExceptConds_and(v_a_1698_, v_snd_1700_, v_snd_1702_);
                if v_isShared_1705_ == 0 {
                    lean_ctor_set(v___x_1704_, 1, v___x_1707_);
                    lean_ctor_set(v___x_1704_, 0, v___f_1706_);
                    v___x_1709_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___f_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
                    v___x_1709_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0;
    v___x_1735_ = l_String_toRawSubstring_x27(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(
    mut v_x_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    v___x_1754_ = l_Std_Do_term___u2227_u2091___00__closed__1;
    lean_inc(v_x_1751_);
    v___x_1755_ = l_Lean_Syntax_isOfKind(v_x_1751_, v___x_1754_);
    if v___x_1755_ == 0 {
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1751_);
        v___x_1756_ = lean_box(1);
        v___x_1757_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1757_, 0, v___x_1756_);
        lean_ctor_set(v___x_1757_, 1, v_a_1753_);
        return v___x_1757_;
    } else {
        let mut v_quotContext_1758_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: u8 = 0;
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1758_ = lean_ctor_get(v_a_1752_, 1);
        v_currMacroScope_1759_ = lean_ctor_get(v_a_1752_, 2);
        v_ref_1760_ = lean_ctor_get(v_a_1752_, 5);
        v___x_1761_ = lean_unsigned_to_nat(0);
        v___x_1762_ = l_Lean_Syntax_getArg(v_x_1751_, v___x_1761_);
        v___x_1763_ = lean_unsigned_to_nat(2);
        v___x_1764_ = l_Lean_Syntax_getArg(v_x_1751_, v___x_1763_);
        lean_dec(v_x_1751_);
        v___x_1765_ = 0;
        v___x_1766_ = l_Lean_SourceInfo_fromRef(v_ref_1760_, v___x_1765_);
        v___x_1767_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1768_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1);
        v___x_1769_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3;
        lean_inc(v_currMacroScope_1759_);
        lean_inc(v_quotContext_1758_);
        v___x_1770_ =
            l_Lean_addMacroScope(v_quotContext_1758_, v___x_1769_, v_currMacroScope_1759_);
        v___x_1771_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6;
        lean_inc_n(v___x_1766_, 2);
        v___x_1772_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1772_, 0, v___x_1766_);
        lean_ctor_set(v___x_1772_, 1, v___x_1768_);
        lean_ctor_set(v___x_1772_, 2, v___x_1770_);
        lean_ctor_set(v___x_1772_, 3, v___x_1771_);
        v___x_1773_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1774_ = l_Lean_Syntax_node2(v___x_1766_, v___x_1773_, v___x_1762_, v___x_1764_);
        v___x_1775_ = l_Lean_Syntax_node2(v___x_1766_, v___x_1767_, v___x_1772_, v___x_1774_);
        v___x_1776_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1776_, 0, v___x_1775_);
        lean_ctor_set(v___x_1776_, 1, v_a_1753_);
        return v___x_1776_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___boxed(
    mut v_x_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1780_: *mut LeanObject = core::ptr::null_mut();
    v_res_1780_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(
            v_x_1777_, v_a_1778_, v_a_1779_,
        );
    lean_dec_ref(v_a_1778_);
    return v_res_1780_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(
    mut v_x_1781_: *mut LeanObject,
    mut v_a_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    v___x_1784_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_1781_);
    v___x_1785_ = l_Lean_Syntax_isOfKind(v_x_1781_, v___x_1784_);
    if v___x_1785_ == 0 {
        let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1781_);
        v___x_1786_ = lean_box(0);
        v___x_1787_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1787_, 0, v___x_1786_);
        lean_ctor_set(v___x_1787_, 1, v_a_1783_);
        return v___x_1787_;
    } else {
        let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: u8 = 0;
        v___x_1788_ = lean_unsigned_to_nat(0);
        v___x_1789_ = l_Lean_Syntax_getArg(v_x_1781_, v___x_1788_);
        v___x_1790_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_1789_);
        v___x_1791_ = l_Lean_Syntax_isOfKind(v___x_1789_, v___x_1790_);
        if v___x_1791_ == 0 {
            let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1789_);
            lean_dec(v_x_1781_);
            v___x_1792_ = lean_box(0);
            v___x_1793_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1793_, 0, v___x_1792_);
            lean_ctor_set(v___x_1793_, 1, v_a_1783_);
            return v___x_1793_;
        } else {
            let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1797_: u8 = 0;
            v___x_1794_ = lean_unsigned_to_nat(1);
            v___x_1795_ = l_Lean_Syntax_getArg(v_x_1781_, v___x_1794_);
            lean_dec(v_x_1781_);
            v___x_1796_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1795_);
            v___x_1797_ = l_Lean_Syntax_matchesNull(v___x_1795_, v___x_1796_);
            if v___x_1797_ == 0 {
                let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1795_);
                lean_dec(v___x_1789_);
                v___x_1798_ = lean_box(0);
                v___x_1799_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1799_, 0, v___x_1798_);
                lean_ctor_set(v___x_1799_, 1, v_a_1783_);
                return v___x_1799_;
            } else {
                let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1802_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1803_: u8 = 0;
                let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
                v___x_1800_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1788_);
                v___x_1801_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1794_);
                lean_dec(v___x_1795_);
                v_ref_1802_ = l_Lean_replaceRef(v___x_1789_, v_a_1782_);
                lean_dec(v___x_1789_);
                v___x_1803_ = 0;
                v___x_1804_ = l_Lean_SourceInfo_fromRef(v_ref_1802_, v___x_1803_);
                lean_dec(v_ref_1802_);
                v___x_1805_ = l_Std_Do_term___u2227_u2091___00__closed__1;
                v___x_1806_ = l_Std_Do_term___u2227_u2091___00__closed__2;
                lean_inc(v___x_1804_);
                v___x_1807_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1807_, 0, v___x_1804_);
                lean_ctor_set(v___x_1807_, 1, v___x_1806_);
                v___x_1808_ = l_Lean_Syntax_node3(
                    v___x_1804_,
                    v___x_1805_,
                    v___x_1800_,
                    v___x_1807_,
                    v___x_1801_,
                );
                v___x_1809_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                lean_ctor_set(v___x_1809_, 1, v_a_1783_);
                return v___x_1809_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(
    mut v_x_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(
        v_x_1810_, v_a_1811_, v_a_1812_,
    );
    lean_dec(v_a_1811_);
    return v_res_1813_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp___lam__0(
    mut v_a_1814_: *mut LeanObject,
    mut v_fst_1815_: *mut LeanObject,
    mut v_fst_1816_: *mut LeanObject,
    mut v_e_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Std_Do_PostShape_args(v_a_1814_);
    lean_inc(v_e_1817_);
    v___x_1819_ = lean_apply_1(v_fst_1815_, v_e_1817_);
    v___x_1820_ = lean_apply_1(v_fst_1816_, v_e_1817_);
    v___x_1821_ = l_Std_Do_SPred_imp(v___x_1818_, v___x_1819_, v___x_1820_);
    return v___x_1821_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp___lam__0___boxed(
    mut v_a_1822_: *mut LeanObject,
    mut v_fst_1823_: *mut LeanObject,
    mut v_fst_1824_: *mut LeanObject,
    mut v_e_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1826_: *mut LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_Do_ExceptConds_imp___lam__0(v_a_1822_, v_fst_1823_, v_fst_1824_, v_e_1825_);
    lean_dec(v_a_1822_);
    return v_res_1826_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp(
    mut v_ps_1827_: *mut LeanObject,
    mut v_x_1828_: *mut LeanObject,
    mut v_y_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___f_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_ps_1827_) {
                0 => {
                    lean_dec(v_y_1829_);
                    lean_dec(v_x_1828_);
                    v___x_1830_ = lean_box(0);
                    return v___x_1830_;
                }
                1 => {
                    v_a_1831_ = lean_ctor_get(v_ps_1827_, 0);
                    lean_inc(v_a_1831_);
                    lean_dec_ref_known(v_ps_1827_, 1);
                    v_ps_1827_ = v_a_1831_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1833_ = lean_ctor_get(v_ps_1827_, 0);
                    lean_inc(v_a_1833_);
                    lean_dec_ref_known(v_ps_1827_, 1);
                    v_fst_1834_ = lean_ctor_get(v_x_1828_, 0);
                    lean_inc(v_fst_1834_);
                    v_snd_1835_ = lean_ctor_get(v_x_1828_, 1);
                    lean_inc(v_snd_1835_);
                    lean_dec(v_x_1828_);
                    v_fst_1836_ = lean_ctor_get(v_y_1829_, 0);
                    v_snd_1837_ = lean_ctor_get(v_y_1829_, 1);
                    v_isSharedCheck_1846_ = (!lean_is_exclusive(v_y_1829_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v___x_1839_ = v_y_1829_;
                        v_isShared_1840_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1837_);
                        lean_inc(v_fst_1836_);
                        lean_dec(v_y_1829_);
                        v___x_1839_ = lean_box(0);
                        v_isShared_1840_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                lean_inc(v_a_1833_);
                v___f_1841_ = lean_alloc_closure(
                    l_Std_Do_ExceptConds_imp___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_1841_, 0, v_a_1833_);
                lean_closure_set(v___f_1841_, 1, v_fst_1834_);
                lean_closure_set(v___f_1841_, 2, v_fst_1836_);
                v___x_1842_ = l_Std_Do_ExceptConds_imp(v_a_1833_, v_snd_1835_, v_snd_1837_);
                if v_isShared_1840_ == 0 {
                    lean_ctor_set(v___x_1839_, 1, v___x_1842_);
                    lean_ctor_set(v___x_1839_, 0, v___f_1841_);
                    v___x_1844_ = v___x_1839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___f_1841_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1()
-> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0;
    v___x_1867_ = l_String_toRawSubstring_x27(v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(
    mut v_x_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    v___x_1886_ = l_Std_Do_term___u2192_u2091___00__closed__1;
    lean_inc(v_x_1883_);
    v___x_1887_ = l_Lean_Syntax_isOfKind(v_x_1883_, v___x_1886_);
    if v___x_1887_ == 0 {
        let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1883_);
        v___x_1888_ = lean_box(1);
        v___x_1889_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1889_, 0, v___x_1888_);
        lean_ctor_set(v___x_1889_, 1, v_a_1885_);
        return v___x_1889_;
    } else {
        let mut v_quotContext_1890_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: u8 = 0;
        let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_1890_ = lean_ctor_get(v_a_1884_, 1);
        v_currMacroScope_1891_ = lean_ctor_get(v_a_1884_, 2);
        v_ref_1892_ = lean_ctor_get(v_a_1884_, 5);
        v___x_1893_ = lean_unsigned_to_nat(0);
        v___x_1894_ = l_Lean_Syntax_getArg(v_x_1883_, v___x_1893_);
        v___x_1895_ = lean_unsigned_to_nat(2);
        v___x_1896_ = l_Lean_Syntax_getArg(v_x_1883_, v___x_1895_);
        lean_dec(v_x_1883_);
        v___x_1897_ = 0;
        v___x_1898_ = l_Lean_SourceInfo_fromRef(v_ref_1892_, v___x_1897_);
        v___x_1899_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1900_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1);
        v___x_1901_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3;
        lean_inc(v_currMacroScope_1891_);
        lean_inc(v_quotContext_1890_);
        v___x_1902_ =
            l_Lean_addMacroScope(v_quotContext_1890_, v___x_1901_, v_currMacroScope_1891_);
        v___x_1903_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6;
        lean_inc_n(v___x_1898_, 2);
        v___x_1904_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_1904_, 0, v___x_1898_);
        lean_ctor_set(v___x_1904_, 1, v___x_1900_);
        lean_ctor_set(v___x_1904_, 2, v___x_1902_);
        lean_ctor_set(v___x_1904_, 3, v___x_1903_);
        v___x_1905_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1906_ = l_Lean_Syntax_node2(v___x_1898_, v___x_1905_, v___x_1894_, v___x_1896_);
        v___x_1907_ = l_Lean_Syntax_node2(v___x_1898_, v___x_1899_, v___x_1904_, v___x_1906_);
        v___x_1908_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1908_, 0, v___x_1907_);
        lean_ctor_set(v___x_1908_, 1, v_a_1885_);
        return v___x_1908_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___boxed(
    mut v_x_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1912_: *mut LeanObject = core::ptr::null_mut();
    v_res_1912_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(
            v_x_1909_, v_a_1910_, v_a_1911_,
        );
    lean_dec_ref(v_a_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(
    mut v_x_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    v___x_1916_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_1913_);
    v___x_1917_ = l_Lean_Syntax_isOfKind(v_x_1913_, v___x_1916_);
    if v___x_1917_ == 0 {
        let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1913_);
        v___x_1918_ = lean_box(0);
        v___x_1919_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1919_, 0, v___x_1918_);
        lean_ctor_set(v___x_1919_, 1, v_a_1915_);
        return v___x_1919_;
    } else {
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: u8 = 0;
        v___x_1920_ = lean_unsigned_to_nat(0);
        v___x_1921_ = l_Lean_Syntax_getArg(v_x_1913_, v___x_1920_);
        v___x_1922_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_1921_);
        v___x_1923_ = l_Lean_Syntax_isOfKind(v___x_1921_, v___x_1922_);
        if v___x_1923_ == 0 {
            let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1921_);
            lean_dec(v_x_1913_);
            v___x_1924_ = lean_box(0);
            v___x_1925_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1925_, 0, v___x_1924_);
            lean_ctor_set(v___x_1925_, 1, v_a_1915_);
            return v___x_1925_;
        } else {
            let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1929_: u8 = 0;
            v___x_1926_ = lean_unsigned_to_nat(1);
            v___x_1927_ = l_Lean_Syntax_getArg(v_x_1913_, v___x_1926_);
            lean_dec(v_x_1913_);
            v___x_1928_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_1927_);
            v___x_1929_ = l_Lean_Syntax_matchesNull(v___x_1927_, v___x_1928_);
            if v___x_1929_ == 0 {
                let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1927_);
                lean_dec(v___x_1921_);
                v___x_1930_ = lean_box(0);
                v___x_1931_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1931_, 0, v___x_1930_);
                lean_ctor_set(v___x_1931_, 1, v_a_1915_);
                return v___x_1931_;
            } else {
                let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_1934_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1935_: u8 = 0;
                let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
                v___x_1932_ = l_Lean_Syntax_getArg(v___x_1927_, v___x_1920_);
                v___x_1933_ = l_Lean_Syntax_getArg(v___x_1927_, v___x_1926_);
                lean_dec(v___x_1927_);
                v_ref_1934_ = l_Lean_replaceRef(v___x_1921_, v_a_1914_);
                lean_dec(v___x_1921_);
                v___x_1935_ = 0;
                v___x_1936_ = l_Lean_SourceInfo_fromRef(v_ref_1934_, v___x_1935_);
                lean_dec(v_ref_1934_);
                v___x_1937_ = l_Std_Do_term___u2192_u2091___00__closed__1;
                v___x_1938_ = l_Std_Do_term___u2192_u2091___00__closed__2;
                lean_inc(v___x_1936_);
                v___x_1939_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1939_, 0, v___x_1936_);
                lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                v___x_1940_ = l_Lean_Syntax_node3(
                    v___x_1936_,
                    v___x_1937_,
                    v___x_1932_,
                    v___x_1939_,
                    v___x_1933_,
                );
                v___x_1941_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1941_, 0, v___x_1940_);
                lean_ctor_set(v___x_1941_, 1, v_a_1915_);
                return v___x_1941_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(
    mut v_x_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
    mut v_a_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(
        v_x_1942_, v_a_1943_, v_a_1944_,
    );
    lean_dec(v_a_1943_);
    return v_res_1945_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13()
-> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Array_mkArray0(lean_box(0));
    return v___x_2015_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15()
-> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14;
    v___x_2018_ = l_String_toRawSubstring_x27(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(
    mut v_x_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    v___x_2038_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1;
    lean_inc(v_x_2035_);
    v___x_2039_ = l_Lean_Syntax_isOfKind(v_x_2035_, v___x_2038_);
    if v___x_2039_ == 0 {
        let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2035_);
        v___x_2040_ = lean_box(1);
        v___x_2041_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2041_, 0, v___x_2040_);
        lean_ctor_set(v___x_2041_, 1, v_a_2037_);
        return v___x_2041_;
    } else {
        let mut v_quotContext_2042_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2043_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: u8 = 0;
        let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2042_ = lean_ctor_get(v_a_2036_, 1);
        v_currMacroScope_2043_ = lean_ctor_get(v_a_2036_, 2);
        v_ref_2044_ = lean_ctor_get(v_a_2036_, 5);
        v___x_2045_ = lean_unsigned_to_nat(1);
        v___x_2046_ = l_Lean_Syntax_getArg(v_x_2035_, v___x_2045_);
        lean_dec(v_x_2035_);
        v___x_2047_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5;
        v___x_2048_ = l_Lean_Syntax_getArgs(v___x_2046_);
        lean_dec(v___x_2046_);
        v___x_2049_ = 0;
        v___x_2050_ = l_Lean_SourceInfo_fromRef(v_ref_2044_, v___x_2049_);
        v___x_2051_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2052_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        lean_inc_n(v___x_2050_, 12);
        v___x_2053_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2053_, 0, v___x_2050_);
        lean_ctor_set(v___x_2053_, 1, v___x_2052_);
        v___x_2054_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2055_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2056_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2057_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2058_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2059_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2059_, 0, v___x_2050_);
        lean_ctor_set(v___x_2059_, 1, v___x_2057_);
        v___x_2060_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11;
        v___x_2061_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12;
        v___x_2062_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2062_, 0, v___x_2050_);
        lean_ctor_set(v___x_2062_, 1, v___x_2061_);
        v___x_2063_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v___x_2064_ = l_Array_append___redArg(v___x_2063_, v___x_2048_);
        lean_dec_ref(v___x_2048_);
        v___x_2065_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2065_, 0, v___x_2050_);
        lean_ctor_set(v___x_2065_, 1, v___x_2047_);
        v___x_2066_ = lean_array_push(v___x_2064_, v___x_2065_);
        v___x_2067_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15);
        v___x_2068_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18;
        lean_inc(v_currMacroScope_2043_);
        lean_inc(v_quotContext_2042_);
        v___x_2069_ =
            l_Lean_addMacroScope(v_quotContext_2042_, v___x_2068_, v_currMacroScope_2043_);
        v___x_2070_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22;
        v___x_2071_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2071_, 0, v___x_2050_);
        lean_ctor_set(v___x_2071_, 1, v___x_2067_);
        lean_ctor_set(v___x_2071_, 2, v___x_2069_);
        lean_ctor_set(v___x_2071_, 3, v___x_2070_);
        v___x_2072_ = lean_array_push(v___x_2066_, v___x_2071_);
        v___x_2073_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2073_, 0, v___x_2050_);
        lean_ctor_set(v___x_2073_, 1, v___x_2056_);
        lean_ctor_set(v___x_2073_, 2, v___x_2072_);
        v___x_2074_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10;
        v___x_2075_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2075_, 0, v___x_2050_);
        lean_ctor_set(v___x_2075_, 1, v___x_2074_);
        v___x_2076_ = l_Lean_Syntax_node3(
            v___x_2050_,
            v___x_2060_,
            v___x_2062_,
            v___x_2073_,
            v___x_2075_,
        );
        v___x_2077_ = l_Lean_Syntax_node2(v___x_2050_, v___x_2058_, v___x_2059_, v___x_2076_);
        v___x_2078_ = l_Lean_Syntax_node1(v___x_2050_, v___x_2056_, v___x_2077_);
        v___x_2079_ = l_Lean_Syntax_node1(v___x_2050_, v___x_2055_, v___x_2078_);
        v___x_2080_ = l_Lean_Syntax_node1(v___x_2050_, v___x_2054_, v___x_2079_);
        v___x_2081_ = l_Lean_Syntax_node2(v___x_2050_, v___x_2051_, v___x_2053_, v___x_2080_);
        v___x_2082_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2082_, 0, v___x_2081_);
        lean_ctor_set(v___x_2082_, 1, v_a_2037_);
        return v___x_2082_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___boxed(
    mut v_x_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2086_: *mut LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(v_x_2083_, v_a_2084_, v_a_2085_);
    lean_dec_ref(v_a_2084_);
    return v_res_2086_;
}
pub unsafe fn l_Std_Do_PostCond_noThrow___redArg(
    mut v_ps_2087_: *mut LeanObject,
    mut v_p_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2087_);
    v___x_2090_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2090_, 0, v_p_2088_);
    lean_ctor_set(v___x_2090_, 1, v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l_Std_Do_PostCond_noThrow(
    mut v_00_u03b1_2091_: *mut LeanObject,
    mut v_ps_2092_: *mut LeanObject,
    mut v_p_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2092_);
    v___x_2095_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2095_, 0, v_p_2093_);
    lean_ctor_set(v___x_2095_, 1, v___x_2094_);
    return v___x_2095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(
    mut v_sz_2148_: usize,
    mut v_i_2149_: usize,
    mut v_bs_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2151_: u8 = 0;
    let mut v_v_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: usize = 0;
    let mut v___x_2156_: usize = 0;
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2151_ = lean_usize_dec_lt(v_i_2149_, v_sz_2148_);
                if v___x_2151_ == 0 {
                    return v_bs_2150_;
                } else {
                    v_v_2152_ = lean_array_uget(v_bs_2150_, v_i_2149_);
                    v___x_2153_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2154_ = lean_array_uset(v_bs_2150_, v_i_2149_, v___x_2153_);
                    v___x_2155_ = 1usize;
                    v___x_2156_ = lean_usize_add(v_i_2149_, v___x_2155_);
                    v___x_2157_ = lean_array_uset(v_bs_x27_2154_, v_i_2149_, v_v_2152_);
                    v_i_2149_ = v___x_2156_;
                    v_bs_2150_ = v___x_2157_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0___boxed(
    mut v_sz_2159_: *mut LeanObject,
    mut v_i_2160_: *mut LeanObject,
    mut v_bs_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2162_: usize = 0;
    let mut v_i_boxed_2163_: usize = 0;
    let mut v_res_2164_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2159_);
    lean_dec(v_sz_2159_);
    v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
    lean_dec(v_i_2160_);
    v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_boxed_2162_, v_i_boxed_2163_, v_bs_2161_);
    return v_res_2164_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1()
-> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v___x_2166_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0;
    v___x_2167_ = l_String_toRawSubstring_x27(v___x_2166_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16()
-> *mut LeanObject {
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15;
    v___x_2202_ = l_String_toRawSubstring_x27(v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(
    mut v_x_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    v___x_2234_ = l_Std_Do_term___u21d3___x3d_x3e___00__closed__1;
    lean_inc(v_x_2231_);
    v___x_2235_ = l_Lean_Syntax_isOfKind(v_x_2231_, v___x_2234_);
    if v___x_2235_ == 0 {
        let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2231_);
        v___x_2236_ = lean_box(1);
        v___x_2237_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2237_, 0, v___x_2236_);
        lean_ctor_set(v___x_2237_, 1, v_a_2233_);
        return v___x_2237_;
    } else {
        let mut v_quotContext_2238_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_2245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: u8 = 0;
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_2280_: usize = 0;
        let mut v___x_2281_: usize = 0;
        let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2238_ = lean_ctor_get(v_a_2232_, 1);
        v_currMacroScope_2239_ = lean_ctor_get(v_a_2232_, 2);
        v_ref_2240_ = lean_ctor_get(v_a_2232_, 5);
        v___x_2241_ = lean_unsigned_to_nat(2);
        v___x_2242_ = l_Lean_Syntax_getArg(v_x_2231_, v___x_2241_);
        v___x_2243_ = lean_unsigned_to_nat(4);
        v___x_2244_ = l_Lean_Syntax_getArg(v_x_2231_, v___x_2243_);
        lean_dec(v_x_2231_);
        v_xs_2245_ = l_Lean_Syntax_getArgs(v___x_2242_);
        lean_dec(v___x_2242_);
        v___x_2246_ = 0;
        v___x_2247_ = l_Lean_SourceInfo_fromRef(v_ref_2240_, v___x_2246_);
        v___x_2248_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2249_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1);
        v___x_2250_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4;
        lean_inc_n(v_currMacroScope_2239_, 2);
        lean_inc_n(v_quotContext_2238_, 2);
        v___x_2251_ =
            l_Lean_addMacroScope(v_quotContext_2238_, v___x_2250_, v_currMacroScope_2239_);
        v___x_2252_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7;
        lean_inc_n(v___x_2247_, 23);
        v___x_2253_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2253_, 0, v___x_2247_);
        lean_ctor_set(v___x_2253_, 1, v___x_2249_);
        lean_ctor_set(v___x_2253_, 2, v___x_2251_);
        lean_ctor_set(v___x_2253_, 3, v___x_2252_);
        v___x_2254_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2255_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9;
        v___x_2256_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11;
        v___x_2257_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12;
        v___x_2258_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2258_, 0, v___x_2247_);
        lean_ctor_set(v___x_2258_, 1, v___x_2257_);
        v___x_2259_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14;
        v___x_2260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
        v___x_2261_ = lean_box(0);
        v___x_2262_ =
            l_Lean_addMacroScope(v_quotContext_2238_, v___x_2261_, v_currMacroScope_2239_);
        v___x_2263_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19;
        v___x_2264_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2264_, 0, v___x_2247_);
        lean_ctor_set(v___x_2264_, 1, v___x_2260_);
        lean_ctor_set(v___x_2264_, 2, v___x_2262_);
        lean_ctor_set(v___x_2264_, 3, v___x_2263_);
        v___x_2265_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2259_, v___x_2264_);
        v___x_2266_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2256_, v___x_2258_, v___x_2265_);
        v___x_2267_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2268_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        v___x_2269_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2269_, 0, v___x_2247_);
        lean_ctor_set(v___x_2269_, 1, v___x_2268_);
        v___x_2270_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2271_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2272_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2273_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2274_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2274_, 0, v___x_2247_);
        lean_ctor_set(v___x_2274_, 1, v___x_2272_);
        v___x_2275_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20;
        v___x_2276_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21;
        v___x_2277_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2277_, 0, v___x_2247_);
        lean_ctor_set(v___x_2277_, 1, v___x_2275_);
        v___x_2278_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23;
        v___x_2279_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v_sz_2280_ = lean_array_size(v_xs_2245_);
        v___x_2281_ = 0usize;
        v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_2280_, v___x_2281_, v_xs_2245_);
        v___x_2283_ = l_Array_append___redArg(v___x_2279_, v___x_2282_);
        lean_dec_ref(v___x_2282_);
        v___x_2284_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2284_, 0, v___x_2247_);
        lean_ctor_set(v___x_2284_, 1, v___x_2254_);
        lean_ctor_set(v___x_2284_, 2, v___x_2283_);
        v___x_2285_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2285_, 0, v___x_2247_);
        lean_ctor_set(v___x_2285_, 1, v___x_2254_);
        lean_ctor_set(v___x_2285_, 2, v___x_2279_);
        v___x_2286_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24;
        v___x_2287_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2287_, 0, v___x_2247_);
        lean_ctor_set(v___x_2287_, 1, v___x_2286_);
        v___x_2288_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26;
        v___x_2289_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27;
        v___x_2290_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2290_, 0, v___x_2247_);
        lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        v___x_2291_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28;
        v___x_2292_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2292_, 0, v___x_2247_);
        lean_ctor_set(v___x_2292_, 1, v___x_2291_);
        lean_inc_ref(v___x_2292_);
        v___x_2293_ = l_Lean_Syntax_node3(
            v___x_2247_,
            v___x_2288_,
            v___x_2290_,
            v___x_2244_,
            v___x_2292_,
        );
        v___x_2294_ = l_Lean_Syntax_node4(
            v___x_2247_,
            v___x_2278_,
            v___x_2284_,
            v___x_2285_,
            v___x_2287_,
            v___x_2293_,
        );
        v___x_2295_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2276_, v___x_2277_, v___x_2294_);
        v___x_2296_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2273_, v___x_2274_, v___x_2295_);
        v___x_2297_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2254_, v___x_2296_);
        v___x_2298_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2271_, v___x_2297_);
        v___x_2299_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2270_, v___x_2298_);
        v___x_2300_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2267_, v___x_2269_, v___x_2299_);
        v___x_2301_ = l_Lean_Syntax_node3(
            v___x_2247_,
            v___x_2255_,
            v___x_2266_,
            v___x_2300_,
            v___x_2292_,
        );
        v___x_2302_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2254_, v___x_2301_);
        v___x_2303_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2248_, v___x_2253_, v___x_2302_);
        v___x_2304_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2304_, 0, v___x_2303_);
        lean_ctor_set(v___x_2304_, 1, v_a_2233_);
        return v___x_2304_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___boxed(
    mut v_x_2305_: *mut LeanObject,
    mut v_a_2306_: *mut LeanObject,
    mut v_a_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2308_: *mut LeanObject = core::ptr::null_mut();
    v_res_2308_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(
            v_x_2305_, v_a_2306_, v_a_2307_,
        );
    lean_dec_ref(v_a_2306_);
    return v_res_2308_;
}
pub unsafe fn l_Std_Do_PostCond_mayThrow___redArg(
    mut v_ps_2309_: *mut LeanObject,
    mut v_p_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2311_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2309_);
    v___x_2312_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2312_, 0, v_p_2310_);
    lean_ctor_set(v___x_2312_, 1, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn l_Std_Do_PostCond_mayThrow(
    mut v_00_u03b1_2313_: *mut LeanObject,
    mut v_ps_2314_: *mut LeanObject,
    mut v_p_2315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2314_);
    v___x_2317_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2317_, 0, v_p_2315_);
    lean_ctor_set(v___x_2317_, 1, v___x_2316_);
    return v___x_2317_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1()
-> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0;
    v___x_2349_ = l_String_toRawSubstring_x27(v___x_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(
    mut v_x_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    v___x_2368_ = l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1;
    lean_inc(v_x_2365_);
    v___x_2369_ = l_Lean_Syntax_isOfKind(v_x_2365_, v___x_2368_);
    if v___x_2369_ == 0 {
        let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2365_);
        v___x_2370_ = lean_box(1);
        v___x_2371_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2371_, 0, v___x_2370_);
        lean_ctor_set(v___x_2371_, 1, v_a_2367_);
        return v___x_2371_;
    } else {
        let mut v_quotContext_2372_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2373_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_2379_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: u8 = 0;
        let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_2414_: usize = 0;
        let mut v___x_2415_: usize = 0;
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
        v_quotContext_2372_ = lean_ctor_get(v_a_2366_, 1);
        v_currMacroScope_2373_ = lean_ctor_get(v_a_2366_, 2);
        v_ref_2374_ = lean_ctor_get(v_a_2366_, 5);
        v___x_2375_ = lean_unsigned_to_nat(2);
        v___x_2376_ = l_Lean_Syntax_getArg(v_x_2365_, v___x_2375_);
        v___x_2377_ = lean_unsigned_to_nat(4);
        v___x_2378_ = l_Lean_Syntax_getArg(v_x_2365_, v___x_2377_);
        lean_dec(v_x_2365_);
        v_xs_2379_ = l_Lean_Syntax_getArgs(v___x_2376_);
        lean_dec(v___x_2376_);
        v___x_2380_ = 0;
        v___x_2381_ = l_Lean_SourceInfo_fromRef(v_ref_2374_, v___x_2380_);
        v___x_2382_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2383_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1);
        v___x_2384_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3;
        lean_inc_n(v_currMacroScope_2373_, 2);
        lean_inc_n(v_quotContext_2372_, 2);
        v___x_2385_ =
            l_Lean_addMacroScope(v_quotContext_2372_, v___x_2384_, v_currMacroScope_2373_);
        v___x_2386_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6;
        lean_inc_n(v___x_2381_, 23);
        v___x_2387_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2387_, 0, v___x_2381_);
        lean_ctor_set(v___x_2387_, 1, v___x_2383_);
        lean_ctor_set(v___x_2387_, 2, v___x_2385_);
        lean_ctor_set(v___x_2387_, 3, v___x_2386_);
        v___x_2388_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2389_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9;
        v___x_2390_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11;
        v___x_2391_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12;
        v___x_2392_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2392_, 0, v___x_2381_);
        lean_ctor_set(v___x_2392_, 1, v___x_2391_);
        v___x_2393_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14;
        v___x_2394_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
        v___x_2395_ = lean_box(0);
        v___x_2396_ =
            l_Lean_addMacroScope(v_quotContext_2372_, v___x_2395_, v_currMacroScope_2373_);
        v___x_2397_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19;
        v___x_2398_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2398_, 0, v___x_2381_);
        lean_ctor_set(v___x_2398_, 1, v___x_2394_);
        lean_ctor_set(v___x_2398_, 2, v___x_2396_);
        lean_ctor_set(v___x_2398_, 3, v___x_2397_);
        v___x_2399_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2393_, v___x_2398_);
        v___x_2400_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2390_, v___x_2392_, v___x_2399_);
        v___x_2401_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2402_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        v___x_2403_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2403_, 0, v___x_2381_);
        lean_ctor_set(v___x_2403_, 1, v___x_2402_);
        v___x_2404_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2405_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2406_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2407_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2408_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2408_, 0, v___x_2381_);
        lean_ctor_set(v___x_2408_, 1, v___x_2406_);
        v___x_2409_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20;
        v___x_2410_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21;
        v___x_2411_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2411_, 0, v___x_2381_);
        lean_ctor_set(v___x_2411_, 1, v___x_2409_);
        v___x_2412_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23;
        v___x_2413_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v_sz_2414_ = lean_array_size(v_xs_2379_);
        v___x_2415_ = 0usize;
        v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_2414_, v___x_2415_, v_xs_2379_);
        v___x_2417_ = l_Array_append___redArg(v___x_2413_, v___x_2416_);
        lean_dec_ref(v___x_2416_);
        v___x_2418_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2418_, 0, v___x_2381_);
        lean_ctor_set(v___x_2418_, 1, v___x_2388_);
        lean_ctor_set(v___x_2418_, 2, v___x_2417_);
        v___x_2419_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_2419_, 0, v___x_2381_);
        lean_ctor_set(v___x_2419_, 1, v___x_2388_);
        lean_ctor_set(v___x_2419_, 2, v___x_2413_);
        v___x_2420_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24;
        v___x_2421_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2421_, 0, v___x_2381_);
        lean_ctor_set(v___x_2421_, 1, v___x_2420_);
        v___x_2422_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26;
        v___x_2423_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27;
        v___x_2424_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2424_, 0, v___x_2381_);
        lean_ctor_set(v___x_2424_, 1, v___x_2423_);
        v___x_2425_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28;
        v___x_2426_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2426_, 0, v___x_2381_);
        lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        lean_inc_ref(v___x_2426_);
        v___x_2427_ = l_Lean_Syntax_node3(
            v___x_2381_,
            v___x_2422_,
            v___x_2424_,
            v___x_2378_,
            v___x_2426_,
        );
        v___x_2428_ = l_Lean_Syntax_node4(
            v___x_2381_,
            v___x_2412_,
            v___x_2418_,
            v___x_2419_,
            v___x_2421_,
            v___x_2427_,
        );
        v___x_2429_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2410_, v___x_2411_, v___x_2428_);
        v___x_2430_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2407_, v___x_2408_, v___x_2429_);
        v___x_2431_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2388_, v___x_2430_);
        v___x_2432_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2405_, v___x_2431_);
        v___x_2433_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2404_, v___x_2432_);
        v___x_2434_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2401_, v___x_2403_, v___x_2433_);
        v___x_2435_ = l_Lean_Syntax_node3(
            v___x_2381_,
            v___x_2389_,
            v___x_2400_,
            v___x_2434_,
            v___x_2426_,
        );
        v___x_2436_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2388_, v___x_2435_);
        v___x_2437_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2382_, v___x_2387_, v___x_2436_);
        v___x_2438_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2438_, 0, v___x_2437_);
        lean_ctor_set(v___x_2438_, 1, v_a_2367_);
        return v___x_2438_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___boxed(
    mut v_x_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2442_: *mut LeanObject = core::ptr::null_mut();
    v_res_2442_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(
            v_x_2439_, v_a_2440_, v_a_2441_,
        );
    lean_dec_ref(v_a_2440_);
    return v_res_2442_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__0(
    mut v_x_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = lean_box(0);
    return v___x_2444_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(
    mut v_x_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Do_instInhabitedPostCond___redArg___lam__0(v_x_2445_);
    lean_dec(v_x_2445_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__1(
    mut v_ps_2447_: *mut LeanObject,
    mut v___f_2448_: *mut LeanObject,
    mut v_x_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Std_Do_PostShape_args(v_ps_2447_);
    v___x_2451_ = l_Std_Do_SVal_curry___redArg(v___x_2450_, lean_box(0));
    return v___x_2451_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(
    mut v_ps_2452_: *mut LeanObject,
    mut v___f_2453_: *mut LeanObject,
    mut v_x_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_res_2455_ =
        l_Std_Do_instInhabitedPostCond___redArg___lam__1(v_ps_2452_, v___f_2453_, v_x_2454_);
    lean_dec(v_x_2454_);
    lean_dec(v_ps_2452_);
    return v_res_2455_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg(
    mut v_ps_2456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ps_2456_);
    v___f_2457_ = lean_alloc_closure(
        l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2457_, 0, v_ps_2456_);
    lean_closure_set(v___f_2457_, 1, lean_box(0));
    v___x_2458_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2456_);
    v___x_2459_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2459_, 0, v___f_2457_);
    lean_ctor_set(v___x_2459_, 1, v___x_2458_);
    return v___x_2459_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond(
    mut v_ps_2460_: *mut LeanObject,
    mut v_00_u03b1_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Std_Do_instInhabitedPostCond___redArg(v_ps_2460_);
    return v___x_2462_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1()
-> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0;
    v___x_2483_ = l_String_toRawSubstring_x27(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(
    mut v_x_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    v___x_2501_ = l_Std_Do_term___u22a2_u209a___00__closed__1;
    lean_inc(v_x_2498_);
    v___x_2502_ = l_Lean_Syntax_isOfKind(v_x_2498_, v___x_2501_);
    if v___x_2502_ == 0 {
        let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2498_);
        v___x_2503_ = lean_box(1);
        v___x_2504_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2504_, 0, v___x_2503_);
        lean_ctor_set(v___x_2504_, 1, v_a_2500_);
        return v___x_2504_;
    } else {
        let mut v_quotContext_2505_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2506_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2512_: u8 = 0;
        let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2505_ = lean_ctor_get(v_a_2499_, 1);
        v_currMacroScope_2506_ = lean_ctor_get(v_a_2499_, 2);
        v_ref_2507_ = lean_ctor_get(v_a_2499_, 5);
        v___x_2508_ = lean_unsigned_to_nat(0);
        v___x_2509_ = l_Lean_Syntax_getArg(v_x_2498_, v___x_2508_);
        v___x_2510_ = lean_unsigned_to_nat(2);
        v___x_2511_ = l_Lean_Syntax_getArg(v_x_2498_, v___x_2510_);
        lean_dec(v_x_2498_);
        v___x_2512_ = 0;
        v___x_2513_ = l_Lean_SourceInfo_fromRef(v_ref_2507_, v___x_2512_);
        v___x_2514_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2515_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1);
        v___x_2516_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2;
        lean_inc(v_currMacroScope_2506_);
        lean_inc(v_quotContext_2505_);
        v___x_2517_ =
            l_Lean_addMacroScope(v_quotContext_2505_, v___x_2516_, v_currMacroScope_2506_);
        v___x_2518_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5;
        lean_inc_n(v___x_2513_, 2);
        v___x_2519_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2519_, 0, v___x_2513_);
        lean_ctor_set(v___x_2519_, 1, v___x_2515_);
        lean_ctor_set(v___x_2519_, 2, v___x_2517_);
        lean_ctor_set(v___x_2519_, 3, v___x_2518_);
        v___x_2520_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2521_ = l_Lean_Syntax_node2(v___x_2513_, v___x_2520_, v___x_2509_, v___x_2511_);
        v___x_2522_ = l_Lean_Syntax_node2(v___x_2513_, v___x_2514_, v___x_2519_, v___x_2521_);
        v___x_2523_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2523_, 0, v___x_2522_);
        lean_ctor_set(v___x_2523_, 1, v_a_2500_);
        return v___x_2523_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___boxed(
    mut v_x_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
    mut v_a_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2527_: *mut LeanObject = core::ptr::null_mut();
    v_res_2527_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(
            v_x_2524_, v_a_2525_, v_a_2526_,
        );
    lean_dec_ref(v_a_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(
    mut v_x_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
    mut v_a_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    v___x_2531_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_2528_);
    v___x_2532_ = l_Lean_Syntax_isOfKind(v_x_2528_, v___x_2531_);
    if v___x_2532_ == 0 {
        let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2528_);
        v___x_2533_ = lean_box(0);
        v___x_2534_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2534_, 0, v___x_2533_);
        lean_ctor_set(v___x_2534_, 1, v_a_2530_);
        return v___x_2534_;
    } else {
        let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2538_: u8 = 0;
        v___x_2535_ = lean_unsigned_to_nat(0);
        v___x_2536_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2535_);
        v___x_2537_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_2536_);
        v___x_2538_ = l_Lean_Syntax_isOfKind(v___x_2536_, v___x_2537_);
        if v___x_2538_ == 0 {
            let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2536_);
            lean_dec(v_x_2528_);
            v___x_2539_ = lean_box(0);
            v___x_2540_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2540_, 0, v___x_2539_);
            lean_ctor_set(v___x_2540_, 1, v_a_2530_);
            return v___x_2540_;
        } else {
            let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2544_: u8 = 0;
            v___x_2541_ = lean_unsigned_to_nat(1);
            v___x_2542_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2541_);
            lean_dec(v_x_2528_);
            v___x_2543_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_2542_);
            v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2542_, v___x_2543_);
            if v___x_2544_ == 0 {
                let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2542_);
                lean_dec(v___x_2536_);
                v___x_2545_ = lean_box(0);
                v___x_2546_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                lean_ctor_set(v___x_2546_, 1, v_a_2530_);
                return v___x_2546_;
            } else {
                let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_2549_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2550_: u8 = 0;
                let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
                v___x_2547_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2535_);
                v___x_2548_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2541_);
                lean_dec(v___x_2542_);
                v_ref_2549_ = l_Lean_replaceRef(v___x_2536_, v_a_2529_);
                lean_dec(v___x_2536_);
                v___x_2550_ = 0;
                v___x_2551_ = l_Lean_SourceInfo_fromRef(v_ref_2549_, v___x_2550_);
                lean_dec(v_ref_2549_);
                v___x_2552_ = l_Std_Do_term___u22a2_u209a___00__closed__1;
                v___x_2553_ = l_Std_Do_term___u22a2_u209a___00__closed__2;
                lean_inc(v___x_2551_);
                v___x_2554_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2554_, 0, v___x_2551_);
                lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                v___x_2555_ = l_Lean_Syntax_node3(
                    v___x_2551_,
                    v___x_2552_,
                    v___x_2547_,
                    v___x_2554_,
                    v___x_2548_,
                );
                v___x_2556_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2556_, 0, v___x_2555_);
                lean_ctor_set(v___x_2556_, 1, v_a_2530_);
                return v___x_2556_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(
    mut v_x_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2560_: *mut LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(
        v_x_2557_, v_a_2558_, v_a_2559_,
    );
    lean_dec(v_a_2558_);
    return v_res_2560_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg___lam__0(
    mut v_ps_2561_: *mut LeanObject,
    mut v_fst_2562_: *mut LeanObject,
    mut v_fst_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    v___x_2565_ = l_Std_Do_PostShape_args(v_ps_2561_);
    lean_inc(v_a_2564_);
    v___x_2566_ = lean_apply_1(v_fst_2562_, v_a_2564_);
    v___x_2567_ = lean_apply_1(v_fst_2563_, v_a_2564_);
    v___x_2568_ = l_Std_Do_SPred_and(v___x_2565_, v___x_2566_, v___x_2567_);
    return v___x_2568_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg___lam__0___boxed(
    mut v_ps_2569_: *mut LeanObject,
    mut v_fst_2570_: *mut LeanObject,
    mut v_fst_2571_: *mut LeanObject,
    mut v_a_2572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2573_: *mut LeanObject = core::ptr::null_mut();
    v_res_2573_ =
        l_Std_Do_PostCond_and___redArg___lam__0(v_ps_2569_, v_fst_2570_, v_fst_2571_, v_a_2572_);
    lean_dec(v_ps_2569_);
    return v_res_2573_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg(
    mut v_ps_2574_: *mut LeanObject,
    mut v_p_2575_: *mut LeanObject,
    mut v_q_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___f_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2577_ = lean_ctor_get(v_p_2575_, 0);
                lean_inc(v_fst_2577_);
                v_snd_2578_ = lean_ctor_get(v_p_2575_, 1);
                lean_inc(v_snd_2578_);
                lean_dec_ref(v_p_2575_);
                v_fst_2579_ = lean_ctor_get(v_q_2576_, 0);
                v_snd_2580_ = lean_ctor_get(v_q_2576_, 1);
                v_isSharedCheck_2589_ = (!lean_is_exclusive(v_q_2576_)) as u8;
                if v_isSharedCheck_2589_ == 0 {
                    v___x_2582_ = v_q_2576_;
                    v_isShared_2583_ = v_isSharedCheck_2589_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2580_);
                    lean_inc(v_fst_2579_);
                    lean_dec(v_q_2576_);
                    v___x_2582_ = lean_box(0);
                    v_isShared_2583_ = v_isSharedCheck_2589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ps_2574_);
                v___f_2584_ = lean_alloc_closure(
                    l_Std_Do_PostCond_and___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2584_, 0, v_ps_2574_);
                lean_closure_set(v___f_2584_, 1, v_fst_2577_);
                lean_closure_set(v___f_2584_, 2, v_fst_2579_);
                v___x_2585_ = l_Std_Do_ExceptConds_and(v_ps_2574_, v_snd_2578_, v_snd_2580_);
                if v_isShared_2583_ == 0 {
                    lean_ctor_set(v___x_2582_, 1, v___x_2585_);
                    lean_ctor_set(v___x_2582_, 0, v___f_2584_);
                    v___x_2587_ = v___x_2582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___f_2584_);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2585_);
                    v___x_2587_ = v_reuseFailAlloc_2588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PostCond_and(
    mut v_00_u03b1_2590_: *mut LeanObject,
    mut v_ps_2591_: *mut LeanObject,
    mut v_p_2592_: *mut LeanObject,
    mut v_q_2593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___f_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2594_ = lean_ctor_get(v_p_2592_, 0);
                lean_inc(v_fst_2594_);
                v_snd_2595_ = lean_ctor_get(v_p_2592_, 1);
                lean_inc(v_snd_2595_);
                lean_dec_ref(v_p_2592_);
                v_fst_2596_ = lean_ctor_get(v_q_2593_, 0);
                v_snd_2597_ = lean_ctor_get(v_q_2593_, 1);
                v_isSharedCheck_2606_ = (!lean_is_exclusive(v_q_2593_)) as u8;
                if v_isSharedCheck_2606_ == 0 {
                    v___x_2599_ = v_q_2593_;
                    v_isShared_2600_ = v_isSharedCheck_2606_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2597_);
                    lean_inc(v_fst_2596_);
                    lean_dec(v_q_2593_);
                    v___x_2599_ = lean_box(0);
                    v_isShared_2600_ = v_isSharedCheck_2606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ps_2591_);
                v___f_2601_ = lean_alloc_closure(
                    l_Std_Do_PostCond_and___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2601_, 0, v_ps_2591_);
                lean_closure_set(v___f_2601_, 1, v_fst_2594_);
                lean_closure_set(v___f_2601_, 2, v_fst_2596_);
                v___x_2602_ = l_Std_Do_ExceptConds_and(v_ps_2591_, v_snd_2595_, v_snd_2597_);
                if v_isShared_2600_ == 0 {
                    lean_ctor_set(v___x_2599_, 1, v___x_2602_);
                    lean_ctor_set(v___x_2599_, 0, v___f_2601_);
                    v___x_2604_ = v___x_2599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___f_2601_);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2602_);
                    v___x_2604_ = v_reuseFailAlloc_2605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1()
-> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0;
    v___x_2627_ = l_String_toRawSubstring_x27(v___x_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(
    mut v_x_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u8 = 0;
    v___x_2645_ = l_Std_Do_term___u2227_u209a___00__closed__1;
    lean_inc(v_x_2642_);
    v___x_2646_ = l_Lean_Syntax_isOfKind(v_x_2642_, v___x_2645_);
    if v___x_2646_ == 0 {
        let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2642_);
        v___x_2647_ = lean_box(1);
        v___x_2648_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2648_, 0, v___x_2647_);
        lean_ctor_set(v___x_2648_, 1, v_a_2644_);
        return v___x_2648_;
    } else {
        let mut v_quotContext_2649_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2650_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2656_: u8 = 0;
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
        v_quotContext_2649_ = lean_ctor_get(v_a_2643_, 1);
        v_currMacroScope_2650_ = lean_ctor_get(v_a_2643_, 2);
        v_ref_2651_ = lean_ctor_get(v_a_2643_, 5);
        v___x_2652_ = lean_unsigned_to_nat(0);
        v___x_2653_ = l_Lean_Syntax_getArg(v_x_2642_, v___x_2652_);
        v___x_2654_ = lean_unsigned_to_nat(2);
        v___x_2655_ = l_Lean_Syntax_getArg(v_x_2642_, v___x_2654_);
        lean_dec(v_x_2642_);
        v___x_2656_ = 0;
        v___x_2657_ = l_Lean_SourceInfo_fromRef(v_ref_2651_, v___x_2656_);
        v___x_2658_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2659_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1);
        v___x_2660_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2;
        lean_inc(v_currMacroScope_2650_);
        lean_inc(v_quotContext_2649_);
        v___x_2661_ =
            l_Lean_addMacroScope(v_quotContext_2649_, v___x_2660_, v_currMacroScope_2650_);
        v___x_2662_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5;
        lean_inc_n(v___x_2657_, 2);
        v___x_2663_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2663_, 0, v___x_2657_);
        lean_ctor_set(v___x_2663_, 1, v___x_2659_);
        lean_ctor_set(v___x_2663_, 2, v___x_2661_);
        lean_ctor_set(v___x_2663_, 3, v___x_2662_);
        v___x_2664_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2665_ = l_Lean_Syntax_node2(v___x_2657_, v___x_2664_, v___x_2653_, v___x_2655_);
        v___x_2666_ = l_Lean_Syntax_node2(v___x_2657_, v___x_2658_, v___x_2663_, v___x_2665_);
        v___x_2667_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2667_, 0, v___x_2666_);
        lean_ctor_set(v___x_2667_, 1, v_a_2644_);
        return v___x_2667_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___boxed(
    mut v_x_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
    mut v_a_2670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2671_: *mut LeanObject = core::ptr::null_mut();
    v_res_2671_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(
            v_x_2668_, v_a_2669_, v_a_2670_,
        );
    lean_dec_ref(v_a_2669_);
    return v_res_2671_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(
    mut v_x_2672_: *mut LeanObject,
    mut v_a_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    v___x_2675_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_2672_);
    v___x_2676_ = l_Lean_Syntax_isOfKind(v_x_2672_, v___x_2675_);
    if v___x_2676_ == 0 {
        let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2672_);
        v___x_2677_ = lean_box(0);
        v___x_2678_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2678_, 0, v___x_2677_);
        lean_ctor_set(v___x_2678_, 1, v_a_2674_);
        return v___x_2678_;
    } else {
        let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        v___x_2679_ = lean_unsigned_to_nat(0);
        v___x_2680_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2679_);
        v___x_2681_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_2680_);
        v___x_2682_ = l_Lean_Syntax_isOfKind(v___x_2680_, v___x_2681_);
        if v___x_2682_ == 0 {
            let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2680_);
            lean_dec(v_x_2672_);
            v___x_2683_ = lean_box(0);
            v___x_2684_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2684_, 0, v___x_2683_);
            lean_ctor_set(v___x_2684_, 1, v_a_2674_);
            return v___x_2684_;
        } else {
            let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2688_: u8 = 0;
            v___x_2685_ = lean_unsigned_to_nat(1);
            v___x_2686_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2685_);
            lean_dec(v_x_2672_);
            v___x_2687_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_2686_);
            v___x_2688_ = l_Lean_Syntax_matchesNull(v___x_2686_, v___x_2687_);
            if v___x_2688_ == 0 {
                let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2686_);
                lean_dec(v___x_2680_);
                v___x_2689_ = lean_box(0);
                v___x_2690_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2690_, 0, v___x_2689_);
                lean_ctor_set(v___x_2690_, 1, v_a_2674_);
                return v___x_2690_;
            } else {
                let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_2693_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2694_: u8 = 0;
                let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
                v___x_2691_ = l_Lean_Syntax_getArg(v___x_2686_, v___x_2679_);
                v___x_2692_ = l_Lean_Syntax_getArg(v___x_2686_, v___x_2685_);
                lean_dec(v___x_2686_);
                v_ref_2693_ = l_Lean_replaceRef(v___x_2680_, v_a_2673_);
                lean_dec(v___x_2680_);
                v___x_2694_ = 0;
                v___x_2695_ = l_Lean_SourceInfo_fromRef(v_ref_2693_, v___x_2694_);
                lean_dec(v_ref_2693_);
                v___x_2696_ = l_Std_Do_term___u2227_u209a___00__closed__1;
                v___x_2697_ = l_Std_Do_term___u2227_u209a___00__closed__2;
                lean_inc(v___x_2695_);
                v___x_2698_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2698_, 0, v___x_2695_);
                lean_ctor_set(v___x_2698_, 1, v___x_2697_);
                v___x_2699_ = l_Lean_Syntax_node3(
                    v___x_2695_,
                    v___x_2696_,
                    v___x_2691_,
                    v___x_2698_,
                    v___x_2692_,
                );
                v___x_2700_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2700_, 0, v___x_2699_);
                lean_ctor_set(v___x_2700_, 1, v_a_2674_);
                return v___x_2700_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(
    mut v_x_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2704_: *mut LeanObject = core::ptr::null_mut();
    v_res_2704_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(
        v_x_2701_, v_a_2702_, v_a_2703_,
    );
    lean_dec(v_a_2702_);
    return v_res_2704_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg___lam__0(
    mut v_ps_2705_: *mut LeanObject,
    mut v_fst_2706_: *mut LeanObject,
    mut v_fst_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    v___x_2709_ = l_Std_Do_PostShape_args(v_ps_2705_);
    lean_inc(v_a_2708_);
    v___x_2710_ = lean_apply_1(v_fst_2706_, v_a_2708_);
    v___x_2711_ = lean_apply_1(v_fst_2707_, v_a_2708_);
    v___x_2712_ = l_Std_Do_SPred_imp(v___x_2709_, v___x_2710_, v___x_2711_);
    return v___x_2712_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg___lam__0___boxed(
    mut v_ps_2713_: *mut LeanObject,
    mut v_fst_2714_: *mut LeanObject,
    mut v_fst_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2717_: *mut LeanObject = core::ptr::null_mut();
    v_res_2717_ =
        l_Std_Do_PostCond_imp___redArg___lam__0(v_ps_2713_, v_fst_2714_, v_fst_2715_, v_a_2716_);
    lean_dec(v_ps_2713_);
    return v_res_2717_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg(
    mut v_ps_2718_: *mut LeanObject,
    mut v_p_2719_: *mut LeanObject,
    mut v_q_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___f_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2721_ = lean_ctor_get(v_p_2719_, 0);
                lean_inc(v_fst_2721_);
                v_snd_2722_ = lean_ctor_get(v_p_2719_, 1);
                lean_inc(v_snd_2722_);
                lean_dec_ref(v_p_2719_);
                v_fst_2723_ = lean_ctor_get(v_q_2720_, 0);
                v_snd_2724_ = lean_ctor_get(v_q_2720_, 1);
                v_isSharedCheck_2733_ = (!lean_is_exclusive(v_q_2720_)) as u8;
                if v_isSharedCheck_2733_ == 0 {
                    v___x_2726_ = v_q_2720_;
                    v_isShared_2727_ = v_isSharedCheck_2733_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2724_);
                    lean_inc(v_fst_2723_);
                    lean_dec(v_q_2720_);
                    v___x_2726_ = lean_box(0);
                    v_isShared_2727_ = v_isSharedCheck_2733_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ps_2718_);
                v___f_2728_ = lean_alloc_closure(
                    l_Std_Do_PostCond_imp___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2728_, 0, v_ps_2718_);
                lean_closure_set(v___f_2728_, 1, v_fst_2721_);
                lean_closure_set(v___f_2728_, 2, v_fst_2723_);
                v___x_2729_ = l_Std_Do_ExceptConds_imp(v_ps_2718_, v_snd_2722_, v_snd_2724_);
                if v_isShared_2727_ == 0 {
                    lean_ctor_set(v___x_2726_, 1, v___x_2729_);
                    lean_ctor_set(v___x_2726_, 0, v___f_2728_);
                    v___x_2731_ = v___x_2726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___f_2728_);
                    lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2729_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PostCond_imp(
    mut v_00_u03b1_2734_: *mut LeanObject,
    mut v_ps_2735_: *mut LeanObject,
    mut v_p_2736_: *mut LeanObject,
    mut v_q_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___f_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2738_ = lean_ctor_get(v_p_2736_, 0);
                lean_inc(v_fst_2738_);
                v_snd_2739_ = lean_ctor_get(v_p_2736_, 1);
                lean_inc(v_snd_2739_);
                lean_dec_ref(v_p_2736_);
                v_fst_2740_ = lean_ctor_get(v_q_2737_, 0);
                v_snd_2741_ = lean_ctor_get(v_q_2737_, 1);
                v_isSharedCheck_2750_ = (!lean_is_exclusive(v_q_2737_)) as u8;
                if v_isSharedCheck_2750_ == 0 {
                    v___x_2743_ = v_q_2737_;
                    v_isShared_2744_ = v_isSharedCheck_2750_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2741_);
                    lean_inc(v_fst_2740_);
                    lean_dec(v_q_2737_);
                    v___x_2743_ = lean_box(0);
                    v_isShared_2744_ = v_isSharedCheck_2750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ps_2735_);
                v___f_2745_ = lean_alloc_closure(
                    l_Std_Do_PostCond_imp___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2745_, 0, v_ps_2735_);
                lean_closure_set(v___f_2745_, 1, v_fst_2738_);
                lean_closure_set(v___f_2745_, 2, v_fst_2740_);
                v___x_2746_ = l_Std_Do_ExceptConds_imp(v_ps_2735_, v_snd_2739_, v_snd_2741_);
                if v_isShared_2744_ == 0 {
                    lean_ctor_set(v___x_2743_, 1, v___x_2746_);
                    lean_ctor_set(v___x_2743_, 0, v___f_2745_);
                    v___x_2748_ = v___x_2743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___f_2745_);
                    lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2746_);
                    v___x_2748_ = v_reuseFailAlloc_2749_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1()
-> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0;
    v___x_2771_ = l_String_toRawSubstring_x27(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(
    mut v_x_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: u8 = 0;
    v___x_2789_ = l_Std_Do_term___u2192_u209a___00__closed__1;
    lean_inc(v_x_2786_);
    v___x_2790_ = l_Lean_Syntax_isOfKind(v_x_2786_, v___x_2789_);
    if v___x_2790_ == 0 {
        let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2786_);
        v___x_2791_ = lean_box(1);
        v___x_2792_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2792_, 0, v___x_2791_);
        lean_ctor_set(v___x_2792_, 1, v_a_2788_);
        return v___x_2792_;
    } else {
        let mut v_quotContext_2793_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2794_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2800_: u8 = 0;
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
        v_quotContext_2793_ = lean_ctor_get(v_a_2787_, 1);
        v_currMacroScope_2794_ = lean_ctor_get(v_a_2787_, 2);
        v_ref_2795_ = lean_ctor_get(v_a_2787_, 5);
        v___x_2796_ = lean_unsigned_to_nat(0);
        v___x_2797_ = l_Lean_Syntax_getArg(v_x_2786_, v___x_2796_);
        v___x_2798_ = lean_unsigned_to_nat(2);
        v___x_2799_ = l_Lean_Syntax_getArg(v_x_2786_, v___x_2798_);
        lean_dec(v_x_2786_);
        v___x_2800_ = 0;
        v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2795_, v___x_2800_);
        v___x_2802_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2803_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1);
        v___x_2804_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2;
        lean_inc(v_currMacroScope_2794_);
        lean_inc(v_quotContext_2793_);
        v___x_2805_ =
            l_Lean_addMacroScope(v_quotContext_2793_, v___x_2804_, v_currMacroScope_2794_);
        v___x_2806_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5;
        lean_inc_n(v___x_2801_, 2);
        v___x_2807_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2807_, 0, v___x_2801_);
        lean_ctor_set(v___x_2807_, 1, v___x_2803_);
        lean_ctor_set(v___x_2807_, 2, v___x_2805_);
        lean_ctor_set(v___x_2807_, 3, v___x_2806_);
        v___x_2808_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2809_ = l_Lean_Syntax_node2(v___x_2801_, v___x_2808_, v___x_2797_, v___x_2799_);
        v___x_2810_ = l_Lean_Syntax_node2(v___x_2801_, v___x_2802_, v___x_2807_, v___x_2809_);
        v___x_2811_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2811_, 0, v___x_2810_);
        lean_ctor_set(v___x_2811_, 1, v_a_2788_);
        return v___x_2811_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___boxed(
    mut v_x_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2815_: *mut LeanObject = core::ptr::null_mut();
    v_res_2815_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(
            v_x_2812_, v_a_2813_, v_a_2814_,
        );
    lean_dec_ref(v_a_2813_);
    return v_res_2815_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(
    mut v_x_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    v___x_2819_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    lean_inc(v_x_2816_);
    v___x_2820_ = l_Lean_Syntax_isOfKind(v_x_2816_, v___x_2819_);
    if v___x_2820_ == 0 {
        let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2816_);
        v___x_2821_ = lean_box(0);
        v___x_2822_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2822_, 0, v___x_2821_);
        lean_ctor_set(v___x_2822_, 1, v_a_2818_);
        return v___x_2822_;
    } else {
        let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: u8 = 0;
        v___x_2823_ = lean_unsigned_to_nat(0);
        v___x_2824_ = l_Lean_Syntax_getArg(v_x_2816_, v___x_2823_);
        v___x_2825_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        lean_inc(v___x_2824_);
        v___x_2826_ = l_Lean_Syntax_isOfKind(v___x_2824_, v___x_2825_);
        if v___x_2826_ == 0 {
            let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2824_);
            lean_dec(v_x_2816_);
            v___x_2827_ = lean_box(0);
            v___x_2828_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2828_, 0, v___x_2827_);
            lean_ctor_set(v___x_2828_, 1, v_a_2818_);
            return v___x_2828_;
        } else {
            let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2832_: u8 = 0;
            v___x_2829_ = lean_unsigned_to_nat(1);
            v___x_2830_ = l_Lean_Syntax_getArg(v_x_2816_, v___x_2829_);
            lean_dec(v_x_2816_);
            v___x_2831_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_2830_);
            v___x_2832_ = l_Lean_Syntax_matchesNull(v___x_2830_, v___x_2831_);
            if v___x_2832_ == 0 {
                let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2830_);
                lean_dec(v___x_2824_);
                v___x_2833_ = lean_box(0);
                v___x_2834_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2834_, 0, v___x_2833_);
                lean_ctor_set(v___x_2834_, 1, v_a_2818_);
                return v___x_2834_;
            } else {
                let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_2837_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2838_: u8 = 0;
                let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
                v___x_2835_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2823_);
                v___x_2836_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2829_);
                lean_dec(v___x_2830_);
                v_ref_2837_ = l_Lean_replaceRef(v___x_2824_, v_a_2817_);
                lean_dec(v___x_2824_);
                v___x_2838_ = 0;
                v___x_2839_ = l_Lean_SourceInfo_fromRef(v_ref_2837_, v___x_2838_);
                lean_dec(v_ref_2837_);
                v___x_2840_ = l_Std_Do_term___u2192_u209a___00__closed__1;
                v___x_2841_ = l_Std_Do_term___u2192_u209a___00__closed__2;
                lean_inc(v___x_2839_);
                v___x_2842_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2842_, 0, v___x_2839_);
                lean_ctor_set(v___x_2842_, 1, v___x_2841_);
                v___x_2843_ = l_Lean_Syntax_node3(
                    v___x_2839_,
                    v___x_2840_,
                    v___x_2835_,
                    v___x_2842_,
                    v___x_2836_,
                );
                v___x_2844_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2844_, 0, v___x_2843_);
                lean_ctor_set(v___x_2844_, 1, v_a_2818_);
                return v___x_2844_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(
    mut v_x_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2848_: *mut LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(
        v_x_2845_, v_a_2846_, v_a_2847_,
    );
    lean_dec(v_a_2846_);
    return v_res_2848_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_PostCond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_PostCond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_PostCond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PostCond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_PostCond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_PostCond(builtin);
}

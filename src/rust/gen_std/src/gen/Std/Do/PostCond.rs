// Lean compiler output
// Module: Std.Do.PostCond
// Imports: Std.Do.SPred
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uset, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Do::SPred::SPred::{
    l_Std_Do_SPred_and, l_Std_Do_SPred_imp, l_Std_Do_SPred_pure___redArg,
};
use crate::r#gen::Std::Do::SPred::SVal::l_Std_Do_SVal_curry___redArg;
use crate::r#gen::Std::Do::SPred::{initialize_Std_Do_SPred, runtime_initialize_Std_Do_SPred};
pub static l_Std_Do_term___u22a2_u2091___00__closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__2_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u22a2_u2091___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__2_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u22a2_u2091___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__2_value)
                as *mut leanh::LeanObject,
            6035889643370630703 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__4_value: leanh::LeanStringObject<8> =
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
static mut l_Std_Do_term___u22a2_u2091___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__4_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__6_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u22a2_u2091___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u2091___00__closed__12_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__3_value)
                as *mut leanh::LeanObject,
            (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u2091___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u22a2_u2091__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17055763123476927371 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut leanh::LeanObject,13614334605615213219 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17808102113152393460 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut leanh::LeanObject,7198879216713715016 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2227_u2091___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u2227_u2091___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            11687468331848102906 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2227_u2091___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u2091___00__closed__6_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((36 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u2091___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u2227_u2091__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17055763123476927371 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut leanh::LeanObject,14567852056292133 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17808102113152393460 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut leanh::LeanObject,8609142911669095622 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2192_u2091___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u2192_u2091___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            4432936103724110417 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2192_u2091___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u2091___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u2091___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u2192_u2091__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u2091___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 46, 105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17055763123476927371 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut leanh::LeanObject,4282481912481944283 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value) as *mut leanh::LeanObject,17808102113152393460 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut leanh::LeanObject,6967440820911327760 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value)
            as *mut leanh::LeanObject,
        17707010111776501109 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value:
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
    m_data: [44, 0],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
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
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 11,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value)
            as *mut leanh::LeanObject,
        1 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_termPost_u27e8___x2c_x2c_u27e9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value) as *mut leanh::LeanObject,16173796135615239867 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 97, 99, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value) as *mut leanh::LeanObject,14997215300048349804 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value) as *mut leanh::LeanObject,13429426995999683896 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 85, 110, 105, 116, 46, 117, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 85, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 116, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value) as *mut leanh::LeanObject,11091137386503903511 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value) as *mut leanh::LeanObject,14036392901208071058 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value: leanh::LeanStringObject<
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
    m_length: 10,
    m_data: [116, 101, 114, 109, 95, 226, 135, 147, 95, 61, 62, 95, 0],
};
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            8463861479368259073 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value: leanh::LeanStringObject<
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
    m_data: [103, 114, 111, 117, 112, 0],
};
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
            2214559063752339918 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value: leanh::LeanStringObject<
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
        112, 112, 65, 108, 108, 111, 119, 85, 110, 103, 114, 111, 117, 112, 101, 100, 0,
    ],
};
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
            211807283801307390 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value: leanh::LeanStringObject<
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
    m_data: [109, 97, 110, 121, 49, 0],
};
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value)
                as *mut leanh::LeanObject,
            17243740965612849207 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__9_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value: leanh::LeanStringObject<
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
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u21d3___x3d_x3e___00__closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u21d3___x3d_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 110, 111, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut leanh::LeanObject,3676176009791887579 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value) as *mut leanh::LeanObject,11553573755926099728 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value) as *mut leanh::LeanObject,7043493786777132025 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value) as *mut leanh::LeanObject,16077784126176397009 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value) as *mut leanh::LeanObject,13979102795498516556 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 114, 101, 100, 40, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value)
            as *mut leanh::LeanObject,
        5101830612129297492 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u21d3_x3f___x3d_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,7425120582457359416 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,2940964116523157683 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u22a2_u209a___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u22a2_u209a___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__0_value)
                as *mut leanh::LeanObject,
            597832130936671675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u22a2_u209a___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u22a2_u209a___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u22a2_u209a___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u22a2_u209a__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u22a2_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 101, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut leanh::LeanObject,16792813948254738635 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value) as *mut leanh::LeanObject,717208579114757920 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2227_u209a___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u2227_u209a___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__0_value)
                as *mut leanh::LeanObject,
            15844678083483941974 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2227_u209a___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u2091___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2227_u209a___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((35 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((36 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2227_u209a___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u2227_u209a__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2227_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 97, 110, 100, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut leanh::LeanObject,15623922605380786509 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value) as *mut leanh::LeanObject,9858637187560378014 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2192_u209a___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_term___u2192_u209a___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__0_value)
                as *mut leanh::LeanObject,
            2942702865894185004 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Do_term___u2192_u209a___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_term___u2192_u209a___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_term___u2192_u209a___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_term___u2192_u209a__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_term___u2192_u209a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 46, 105, 109, 112, 0]};
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut leanh::LeanObject,6564238721344519347 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_term___u22a2_u2091___00__closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value) as *mut leanh::LeanObject,11225800798110998584 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_Do_PostShape_ctorIdx(
    mut v_x_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1425_) {
        0 => {
            let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1426_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1426_;
        }
        1 => {
            let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1427_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1427_;
        }
        _ => {
            let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1428_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1428_;
        }
    }
}
pub unsafe fn l_Std_Do_PostShape_ctorIdx___boxed(
    mut v_x_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1430_ = l_Std_Do_PostShape_ctorIdx(v_x_1429_);
    leanh::lean_dec(v_x_1429_);
    return v_res_1430_;
}
pub unsafe fn l_Std_Do_PostShape_ctorElim___redArg(
    mut v_t_1431_: *mut leanh::LeanObject,
    mut v_k_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1431_) == 0 {
        return v_k_1432_;
    } else {
        let mut v_a_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1433_ = leanh::lean_ctor_get(v_t_1431_, 0);
        leanh::lean_inc(v_a_1433_);
        leanh::lean_dec(v_t_1431_);
        v___x_1434_ = leanh::lean_apply_2(v_k_1432_, leanh::lean_box(0), v_a_1433_);
        return v___x_1434_;
    }
}
pub unsafe fn l_Std_Do_PostShape_ctorElim(
    mut v_motive_1435_: *mut leanh::LeanObject,
    mut v_ctorIdx_1436_: *mut leanh::LeanObject,
    mut v_t_1437_: *mut leanh::LeanObject,
    mut v_h_1438_: *mut leanh::LeanObject,
    mut v_k_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1437_, v_k_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_Do_PostShape_ctorElim___boxed(
    mut v_motive_1441_: *mut leanh::LeanObject,
    mut v_ctorIdx_1442_: *mut leanh::LeanObject,
    mut v_t_1443_: *mut leanh::LeanObject,
    mut v_h_1444_: *mut leanh::LeanObject,
    mut v_k_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Std_Do_PostShape_ctorElim(
        v_motive_1441_,
        v_ctorIdx_1442_,
        v_t_1443_,
        v_h_1444_,
        v_k_1445_,
    );
    leanh::lean_dec(v_ctorIdx_1442_);
    return v_res_1446_;
}
pub unsafe fn l_Std_Do_PostShape_pure_elim___redArg(
    mut v_t_1447_: *mut leanh::LeanObject,
    mut v_pure_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1447_, v_pure_1448_);
    return v___x_1449_;
}
pub unsafe fn l_Std_Do_PostShape_pure_elim(
    mut v_motive_1450_: *mut leanh::LeanObject,
    mut v_t_1451_: *mut leanh::LeanObject,
    mut v_h_1452_: *mut leanh::LeanObject,
    mut v_pure_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1451_, v_pure_1453_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Do_PostShape_arg_elim___redArg(
    mut v_t_1455_: *mut leanh::LeanObject,
    mut v_arg_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1455_, v_arg_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Std_Do_PostShape_arg_elim(
    mut v_motive_1458_: *mut leanh::LeanObject,
    mut v_t_1459_: *mut leanh::LeanObject,
    mut v_h_1460_: *mut leanh::LeanObject,
    mut v_arg_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1459_, v_arg_1461_);
    return v___x_1462_;
}
pub unsafe fn l_Std_Do_PostShape_except_elim___redArg(
    mut v_t_1463_: *mut leanh::LeanObject,
    mut v_except_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1463_, v_except_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Std_Do_PostShape_except_elim(
    mut v_motive_1466_: *mut leanh::LeanObject,
    mut v_t_1467_: *mut leanh::LeanObject,
    mut v_h_1468_: *mut leanh::LeanObject,
    mut v_except_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_1467_, v_except_1469_);
    return v___x_1470_;
}
pub unsafe fn l_Std_Do_PostShape_args(
    mut v_x_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1471_) {
                0 => {
                    v___x_1472_ = leanh::lean_box(0);
                    return v___x_1472_;
                }
                1 => {
                    v_a_1473_ = leanh::lean_ctor_get(v_x_1471_, 0);
                    v___x_1474_ = l_Std_Do_PostShape_args(v_a_1473_);
                    v___x_1475_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1475_, 0, leanh::lean_box(0));
                    leanh::lean_ctor_set(v___x_1475_, 1, v___x_1474_);
                    return v___x_1475_;
                }
                _ => {
                    v_a_1476_ = leanh::lean_ctor_get(v_x_1471_, 0);
                    v_x_1471_ = v_a_1476_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_PostShape_args___boxed(
    mut v_x_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Std_Do_PostShape_args(v_x_1478_);
    leanh::lean_dec(v_x_1478_);
    return v_res_1479_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg___lam__0(
    mut v_a_1480_: *mut leanh::LeanObject,
    mut v_00___u03b5_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = l_Std_Do_PostShape_args(v_a_1480_);
    v___x_1483_ = l_Std_Do_SPred_pure___redArg(v___x_1482_);
    return v___x_1483_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg___lam__0___boxed(
    mut v_a_1484_: *mut leanh::LeanObject,
    mut v_00___u03b5_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_Std_Do_ExceptConds_const___redArg___lam__0(v_a_1484_, v_00___u03b5_1485_);
    leanh::lean_dec(v_00___u03b5_1485_);
    leanh::lean_dec(v_a_1484_);
    return v_res_1486_;
}
pub unsafe fn l_Std_Do_ExceptConds_const___redArg(
    mut v_ps_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_ps_1487_) {
                0 => {
                    v___x_1488_ = leanh::lean_box(0);
                    return v___x_1488_;
                }
                1 => {
                    v_a_1489_ = leanh::lean_ctor_get(v_ps_1487_, 0);
                    leanh::lean_inc(v_a_1489_);
                    leanh::lean_dec_ref_known(v_ps_1487_, 1);
                    v_ps_1487_ = v_a_1489_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1491_ = leanh::lean_ctor_get(v_ps_1487_, 0);
                    leanh::lean_inc_n(v_a_1491_, 2);
                    leanh::lean_dec_ref_known(v_ps_1487_, 1);
                    v___f_1492_ = leanh::lean_alloc_closure(
                        l_Std_Do_ExceptConds_const___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1492_, 0, v_a_1491_);
                    v___x_1493_ = l_Std_Do_ExceptConds_const___redArg(v_a_1491_);
                    v___x_1494_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1494_, 0, v___f_1492_);
                    leanh::lean_ctor_set(v___x_1494_, 1, v___x_1493_);
                    return v___x_1494_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_ExceptConds_const(
    mut v_ps_1495_: *mut leanh::LeanObject,
    mut v_p_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1495_);
    return v___x_1497_;
}
pub unsafe fn l_Std_Do_ExceptConds_true(
    mut v_ps_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1498_);
    return v___x_1499_;
}
pub unsafe fn l_Std_Do_ExceptConds_false(
    mut v_ps_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Std_Do_instInhabitedExceptConds(
    mut v_ps_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5;
    v___x_1544_ = l_String_toRawSubstring_x27(v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(
    mut v_x_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
    mut v_a_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    v___x_1572_ = l_Std_Do_term___u22a2_u2091___00__closed__3;
    leanh::lean_inc(v_x_1569_);
    v___x_1573_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1572_);
    if v___x_1573_ == 0 {
        let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1569_);
        v___x_1574_ = leanh::lean_box(1);
        v___x_1575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
        leanh::lean_ctor_set(v___x_1575_, 1, v_a_1571_);
        return v___x_1575_;
    } else {
        let mut v_quotContext_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: u8 = 0;
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1576_ = leanh::lean_ctor_get(v_a_1570_, 1);
        v_currMacroScope_1577_ = leanh::lean_ctor_get(v_a_1570_, 2);
        v_ref_1578_ = leanh::lean_ctor_get(v_a_1570_, 5);
        v___x_1579_ = leanh::lean_unsigned_to_nat(0);
        v___x_1580_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1579_);
        v___x_1581_ = leanh::lean_unsigned_to_nat(2);
        v___x_1582_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1581_);
        leanh::lean_dec(v_x_1569_);
        v___x_1583_ = 0;
        v___x_1584_ = l_Lean_SourceInfo_fromRef(v_ref_1578_, v___x_1583_);
        v___x_1585_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1586_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6);
        v___x_1587_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9;
        leanh::lean_inc(v_currMacroScope_1577_);
        leanh::lean_inc(v_quotContext_1576_);
        v___x_1588_ =
            l_Lean_addMacroScope(v_quotContext_1576_, v___x_1587_, v_currMacroScope_1577_);
        v___x_1589_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14;
        leanh::lean_inc_n(v___x_1584_, 2);
        v___x_1590_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1590_, 0, v___x_1584_);
        leanh::lean_ctor_set(v___x_1590_, 1, v___x_1586_);
        leanh::lean_ctor_set(v___x_1590_, 2, v___x_1588_);
        leanh::lean_ctor_set(v___x_1590_, 3, v___x_1589_);
        v___x_1591_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1592_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1591_, v___x_1580_, v___x_1582_);
        v___x_1593_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1585_, v___x_1590_, v___x_1592_);
        v___x_1594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
        leanh::lean_ctor_set(v___x_1594_, 1, v_a_1571_);
        return v___x_1594_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___boxed(
    mut v_x_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(
            v_x_1595_, v_a_1596_, v_a_1597_,
        );
    leanh::lean_dec_ref(v_a_1596_);
    return v_res_1598_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(
    mut v_x_1602_: *mut leanh::LeanObject,
    mut v_a_1603_: *mut leanh::LeanObject,
    mut v_a_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    v___x_1605_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_1602_);
    v___x_1606_ = l_Lean_Syntax_isOfKind(v_x_1602_, v___x_1605_);
    if v___x_1606_ == 0 {
        let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1602_);
        v___x_1607_ = leanh::lean_box(0);
        v___x_1608_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1608_, 0, v___x_1607_);
        leanh::lean_ctor_set(v___x_1608_, 1, v_a_1604_);
        return v___x_1608_;
    } else {
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1612_: u8 = 0;
        v___x_1609_ = leanh::lean_unsigned_to_nat(0);
        v___x_1610_ = l_Lean_Syntax_getArg(v_x_1602_, v___x_1609_);
        v___x_1611_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_1610_);
        v___x_1612_ = l_Lean_Syntax_isOfKind(v___x_1610_, v___x_1611_);
        if v___x_1612_ == 0 {
            let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1610_);
            leanh::lean_dec(v_x_1602_);
            v___x_1613_ = leanh::lean_box(0);
            v___x_1614_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1614_, 0, v___x_1613_);
            leanh::lean_ctor_set(v___x_1614_, 1, v_a_1604_);
            return v___x_1614_;
        } else {
            let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1618_: u8 = 0;
            v___x_1615_ = leanh::lean_unsigned_to_nat(1);
            v___x_1616_ = l_Lean_Syntax_getArg(v_x_1602_, v___x_1615_);
            leanh::lean_dec(v_x_1602_);
            v___x_1617_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1616_);
            v___x_1618_ = l_Lean_Syntax_matchesNull(v___x_1616_, v___x_1617_);
            if v___x_1618_ == 0 {
                let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1616_);
                leanh::lean_dec(v___x_1610_);
                v___x_1619_ = leanh::lean_box(0);
                v___x_1620_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1620_, 0, v___x_1619_);
                leanh::lean_ctor_set(v___x_1620_, 1, v_a_1604_);
                return v___x_1620_;
            } else {
                let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1624_: u8 = 0;
                let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1621_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1609_);
                v___x_1622_ = l_Lean_Syntax_getArg(v___x_1616_, v___x_1615_);
                leanh::lean_dec(v___x_1616_);
                v_ref_1623_ = l_Lean_replaceRef(v___x_1610_, v_a_1603_);
                leanh::lean_dec(v___x_1610_);
                v___x_1624_ = 0;
                v___x_1625_ = l_Lean_SourceInfo_fromRef(v_ref_1623_, v___x_1624_);
                leanh::lean_dec(v_ref_1623_);
                v___x_1626_ = l_Std_Do_term___u22a2_u2091___00__closed__3;
                v___x_1627_ = l_Std_Do_term___u22a2_u2091___00__closed__6;
                leanh::lean_inc(v___x_1625_);
                v___x_1628_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1628_, 0, v___x_1625_);
                leanh::lean_ctor_set(v___x_1628_, 1, v___x_1627_);
                v___x_1629_ = l_Lean_Syntax_node3(
                    v___x_1625_,
                    v___x_1626_,
                    v___x_1621_,
                    v___x_1628_,
                    v___x_1622_,
                );
                v___x_1630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1630_, 0, v___x_1629_);
                leanh::lean_ctor_set(v___x_1630_, 1, v_a_1604_);
                return v___x_1630_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___boxed(
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v_a_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(
        v_x_1631_, v_a_1632_, v_a_1633_,
    );
    leanh::lean_dec(v_a_1632_);
    return v_res_1634_;
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(
    mut v_ps_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: *mut leanh::LeanObject,
    mut v_y_1637_: *mut leanh::LeanObject,
    mut v_h__1_1638_: *mut leanh::LeanObject,
    mut v_h__2_1639_: *mut leanh::LeanObject,
    mut v_h__3_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_ps_1635_) {
        0 => {
            let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1640_);
            leanh::lean_dec(v_h__2_1639_);
            v___x_1641_ = leanh::lean_apply_2(v_h__1_1638_, v_x_1636_, v_y_1637_);
            return v___x_1641_;
        }
        1 => {
            let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1640_);
            leanh::lean_dec(v_h__1_1638_);
            v_a_1642_ = leanh::lean_ctor_get(v_ps_1635_, 0);
            leanh::lean_inc(v_a_1642_);
            leanh::lean_dec_ref_known(v_ps_1635_, 1);
            v___x_1643_ = leanh::lean_apply_4(
                v_h__2_1639_,
                leanh::lean_box(0),
                v_a_1642_,
                v_x_1636_,
                v_y_1637_,
            );
            return v___x_1643_;
        }
        _ => {
            let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1639_);
            leanh::lean_dec(v_h__1_1638_);
            v_a_1644_ = leanh::lean_ctor_get(v_ps_1635_, 0);
            leanh::lean_inc(v_a_1644_);
            leanh::lean_dec_ref_known(v_ps_1635_, 1);
            v___x_1645_ = leanh::lean_apply_4(
                v_h__3_1640_,
                leanh::lean_box(0),
                v_a_1644_,
                v_x_1636_,
                v_y_1637_,
            );
            return v___x_1645_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter(
    mut v_motive_1646_: *mut leanh::LeanObject,
    mut v_ps_1647_: *mut leanh::LeanObject,
    mut v_x_1648_: *mut leanh::LeanObject,
    mut v_y_1649_: *mut leanh::LeanObject,
    mut v_h__1_1650_: *mut leanh::LeanObject,
    mut v_h__2_1651_: *mut leanh::LeanObject,
    mut v_h__3_1652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_ps_1647_) {
        0 => {
            let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1652_);
            leanh::lean_dec(v_h__2_1651_);
            v___x_1653_ = leanh::lean_apply_2(v_h__1_1650_, v_x_1648_, v_y_1649_);
            return v___x_1653_;
        }
        1 => {
            let mut v_a_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1652_);
            leanh::lean_dec(v_h__1_1650_);
            v_a_1654_ = leanh::lean_ctor_get(v_ps_1647_, 0);
            leanh::lean_inc(v_a_1654_);
            leanh::lean_dec_ref_known(v_ps_1647_, 1);
            v___x_1655_ = leanh::lean_apply_4(
                v_h__2_1651_,
                leanh::lean_box(0),
                v_a_1654_,
                v_x_1648_,
                v_y_1649_,
            );
            return v___x_1655_;
        }
        _ => {
            let mut v_a_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1651_);
            leanh::lean_dec(v_h__1_1650_);
            v_a_1656_ = leanh::lean_ctor_get(v_ps_1647_, 0);
            leanh::lean_inc(v_a_1656_);
            leanh::lean_dec_ref_known(v_ps_1647_, 1);
            v___x_1657_ = leanh::lean_apply_4(
                v_h__3_1652_,
                leanh::lean_box(0),
                v_a_1656_,
                v_x_1648_,
                v_y_1649_,
            );
            return v___x_1657_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(
    mut v_x_1658_: *mut leanh::LeanObject,
    mut v_h__1_1659_: *mut leanh::LeanObject,
    mut v_h__2_1660_: *mut leanh::LeanObject,
    mut v_h__3_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1658_) {
        0 => {
            let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1661_);
            leanh::lean_dec(v_h__2_1660_);
            v___x_1662_ = leanh::lean_box(0);
            v___x_1663_ = leanh::lean_apply_1(v_h__1_1659_, v___x_1662_);
            return v___x_1663_;
        }
        1 => {
            let mut v_a_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1661_);
            leanh::lean_dec(v_h__1_1659_);
            v_a_1664_ = leanh::lean_ctor_get(v_x_1658_, 0);
            leanh::lean_inc(v_a_1664_);
            leanh::lean_dec_ref_known(v_x_1658_, 1);
            v___x_1665_ =
                leanh::lean_apply_2(v_h__2_1660_, leanh::lean_box(0), v_a_1664_);
            return v___x_1665_;
        }
        _ => {
            let mut v_a_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1660_);
            leanh::lean_dec(v_h__1_1659_);
            v_a_1666_ = leanh::lean_ctor_get(v_x_1658_, 0);
            leanh::lean_inc(v_a_1666_);
            leanh::lean_dec_ref_known(v_x_1658_, 1);
            v___x_1667_ =
                leanh::lean_apply_2(v_h__3_1661_, leanh::lean_box(0), v_a_1666_);
            return v___x_1667_;
        }
    }
}
pub unsafe fn l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter(
    mut v_motive_1668_: *mut leanh::LeanObject,
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v_h__1_1670_: *mut leanh::LeanObject,
    mut v_h__2_1671_: *mut leanh::LeanObject,
    mut v_h__3_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1669_) {
        0 => {
            let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1672_);
            leanh::lean_dec(v_h__2_1671_);
            v___x_1673_ = leanh::lean_box(0);
            v___x_1674_ = leanh::lean_apply_1(v_h__1_1670_, v___x_1673_);
            return v___x_1674_;
        }
        1 => {
            let mut v_a_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1672_);
            leanh::lean_dec(v_h__1_1670_);
            v_a_1675_ = leanh::lean_ctor_get(v_x_1669_, 0);
            leanh::lean_inc(v_a_1675_);
            leanh::lean_dec_ref_known(v_x_1669_, 1);
            v___x_1676_ =
                leanh::lean_apply_2(v_h__2_1671_, leanh::lean_box(0), v_a_1675_);
            return v___x_1676_;
        }
        _ => {
            let mut v_a_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1671_);
            leanh::lean_dec(v_h__1_1670_);
            v_a_1677_ = leanh::lean_ctor_get(v_x_1669_, 0);
            leanh::lean_inc(v_a_1677_);
            leanh::lean_dec_ref_known(v_x_1669_, 1);
            v___x_1678_ =
                leanh::lean_apply_2(v_h__3_1672_, leanh::lean_box(0), v_a_1677_);
            return v___x_1678_;
        }
    }
}
pub unsafe fn l_Std_Do_ExceptConds_and___lam__0(
    mut v_a_1679_: *mut leanh::LeanObject,
    mut v_fst_1680_: *mut leanh::LeanObject,
    mut v_fst_1681_: *mut leanh::LeanObject,
    mut v_e_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_Do_PostShape_args(v_a_1679_);
    leanh::lean_inc(v_e_1682_);
    v___x_1684_ = leanh::lean_apply_1(v_fst_1680_, v_e_1682_);
    v___x_1685_ = leanh::lean_apply_1(v_fst_1681_, v_e_1682_);
    v___x_1686_ = l_Std_Do_SPred_and(v___x_1683_, v___x_1684_, v___x_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Std_Do_ExceptConds_and___lam__0___boxed(
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_fst_1688_: *mut leanh::LeanObject,
    mut v_fst_1689_: *mut leanh::LeanObject,
    mut v_e_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1691_ = l_Std_Do_ExceptConds_and___lam__0(v_a_1687_, v_fst_1688_, v_fst_1689_, v_e_1690_);
    leanh::lean_dec(v_a_1687_);
    return v_res_1691_;
}
pub unsafe fn l_Std_Do_ExceptConds_and(
    mut v_ps_1692_: *mut leanh::LeanObject,
    mut v_x_1693_: *mut leanh::LeanObject,
    mut v_y_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___f_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_ps_1692_) {
                0 => {
                    leanh::lean_dec(v_y_1694_);
                    leanh::lean_dec(v_x_1693_);
                    v___x_1695_ = leanh::lean_box(0);
                    return v___x_1695_;
                }
                1 => {
                    v_a_1696_ = leanh::lean_ctor_get(v_ps_1692_, 0);
                    leanh::lean_inc(v_a_1696_);
                    leanh::lean_dec_ref_known(v_ps_1692_, 1);
                    v_ps_1692_ = v_a_1696_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1698_ = leanh::lean_ctor_get(v_ps_1692_, 0);
                    leanh::lean_inc(v_a_1698_);
                    leanh::lean_dec_ref_known(v_ps_1692_, 1);
                    v_fst_1699_ = leanh::lean_ctor_get(v_x_1693_, 0);
                    leanh::lean_inc(v_fst_1699_);
                    v_snd_1700_ = leanh::lean_ctor_get(v_x_1693_, 1);
                    leanh::lean_inc(v_snd_1700_);
                    leanh::lean_dec(v_x_1693_);
                    v_fst_1701_ = leanh::lean_ctor_get(v_y_1694_, 0);
                    v_snd_1702_ = leanh::lean_ctor_get(v_y_1694_, 1);
                    v_isSharedCheck_1711_ = (!leanh::lean_is_exclusive(v_y_1694_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1704_ = v_y_1694_;
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1702_);
                        leanh::lean_inc(v_fst_1701_);
                        leanh::lean_dec(v_y_1694_);
                        v___x_1704_ = leanh::lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                leanh::lean_inc(v_a_1698_);
                v___f_1706_ = leanh::lean_alloc_closure(
                    l_Std_Do_ExceptConds_and___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1706_, 0, v_a_1698_);
                leanh::lean_closure_set(v___f_1706_, 1, v_fst_1699_);
                leanh::lean_closure_set(v___f_1706_, 2, v_fst_1701_);
                v___x_1707_ = l_Std_Do_ExceptConds_and(v_a_1698_, v_snd_1700_, v_snd_1702_);
                if v_isShared_1705_ == 0 {
                    leanh::lean_ctor_set(v___x_1704_, 1, v___x_1707_);
                    leanh::lean_ctor_set(v___x_1704_, 0, v___f_1706_);
                    v___x_1709_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___f_1706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
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
-> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0;
    v___x_1735_ = l_String_toRawSubstring_x27(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(
    mut v_x_1751_: *mut leanh::LeanObject,
    mut v_a_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    v___x_1754_ = l_Std_Do_term___u2227_u2091___00__closed__1;
    leanh::lean_inc(v_x_1751_);
    v___x_1755_ = l_Lean_Syntax_isOfKind(v_x_1751_, v___x_1754_);
    if v___x_1755_ == 0 {
        let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1751_);
        v___x_1756_ = leanh::lean_box(1);
        v___x_1757_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
        leanh::lean_ctor_set(v___x_1757_, 1, v_a_1753_);
        return v___x_1757_;
    } else {
        let mut v_quotContext_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: u8 = 0;
        let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1758_ = leanh::lean_ctor_get(v_a_1752_, 1);
        v_currMacroScope_1759_ = leanh::lean_ctor_get(v_a_1752_, 2);
        v_ref_1760_ = leanh::lean_ctor_get(v_a_1752_, 5);
        v___x_1761_ = leanh::lean_unsigned_to_nat(0);
        v___x_1762_ = l_Lean_Syntax_getArg(v_x_1751_, v___x_1761_);
        v___x_1763_ = leanh::lean_unsigned_to_nat(2);
        v___x_1764_ = l_Lean_Syntax_getArg(v_x_1751_, v___x_1763_);
        leanh::lean_dec(v_x_1751_);
        v___x_1765_ = 0;
        v___x_1766_ = l_Lean_SourceInfo_fromRef(v_ref_1760_, v___x_1765_);
        v___x_1767_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1768_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1);
        v___x_1769_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3;
        leanh::lean_inc(v_currMacroScope_1759_);
        leanh::lean_inc(v_quotContext_1758_);
        v___x_1770_ =
            l_Lean_addMacroScope(v_quotContext_1758_, v___x_1769_, v_currMacroScope_1759_);
        v___x_1771_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6;
        leanh::lean_inc_n(v___x_1766_, 2);
        v___x_1772_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1772_, 0, v___x_1766_);
        leanh::lean_ctor_set(v___x_1772_, 1, v___x_1768_);
        leanh::lean_ctor_set(v___x_1772_, 2, v___x_1770_);
        leanh::lean_ctor_set(v___x_1772_, 3, v___x_1771_);
        v___x_1773_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1774_ = l_Lean_Syntax_node2(v___x_1766_, v___x_1773_, v___x_1762_, v___x_1764_);
        v___x_1775_ = l_Lean_Syntax_node2(v___x_1766_, v___x_1767_, v___x_1772_, v___x_1774_);
        v___x_1776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
        leanh::lean_ctor_set(v___x_1776_, 1, v_a_1753_);
        return v___x_1776_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___boxed(
    mut v_x_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1780_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(
            v_x_1777_, v_a_1778_, v_a_1779_,
        );
    leanh::lean_dec_ref(v_a_1778_);
    return v_res_1780_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(
    mut v_x_1781_: *mut leanh::LeanObject,
    mut v_a_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    v___x_1784_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_1781_);
    v___x_1785_ = l_Lean_Syntax_isOfKind(v_x_1781_, v___x_1784_);
    if v___x_1785_ == 0 {
        let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1781_);
        v___x_1786_ = leanh::lean_box(0);
        v___x_1787_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
        leanh::lean_ctor_set(v___x_1787_, 1, v_a_1783_);
        return v___x_1787_;
    } else {
        let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: u8 = 0;
        v___x_1788_ = leanh::lean_unsigned_to_nat(0);
        v___x_1789_ = l_Lean_Syntax_getArg(v_x_1781_, v___x_1788_);
        v___x_1790_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_1789_);
        v___x_1791_ = l_Lean_Syntax_isOfKind(v___x_1789_, v___x_1790_);
        if v___x_1791_ == 0 {
            let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1789_);
            leanh::lean_dec(v_x_1781_);
            v___x_1792_ = leanh::lean_box(0);
            v___x_1793_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
            leanh::lean_ctor_set(v___x_1793_, 1, v_a_1783_);
            return v___x_1793_;
        } else {
            let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1797_: u8 = 0;
            v___x_1794_ = leanh::lean_unsigned_to_nat(1);
            v___x_1795_ = l_Lean_Syntax_getArg(v_x_1781_, v___x_1794_);
            leanh::lean_dec(v_x_1781_);
            v___x_1796_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1795_);
            v___x_1797_ = l_Lean_Syntax_matchesNull(v___x_1795_, v___x_1796_);
            if v___x_1797_ == 0 {
                let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1795_);
                leanh::lean_dec(v___x_1789_);
                v___x_1798_ = leanh::lean_box(0);
                v___x_1799_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1799_, 0, v___x_1798_);
                leanh::lean_ctor_set(v___x_1799_, 1, v_a_1783_);
                return v___x_1799_;
            } else {
                let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1803_: u8 = 0;
                let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1800_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1788_);
                v___x_1801_ = l_Lean_Syntax_getArg(v___x_1795_, v___x_1794_);
                leanh::lean_dec(v___x_1795_);
                v_ref_1802_ = l_Lean_replaceRef(v___x_1789_, v_a_1782_);
                leanh::lean_dec(v___x_1789_);
                v___x_1803_ = 0;
                v___x_1804_ = l_Lean_SourceInfo_fromRef(v_ref_1802_, v___x_1803_);
                leanh::lean_dec(v_ref_1802_);
                v___x_1805_ = l_Std_Do_term___u2227_u2091___00__closed__1;
                v___x_1806_ = l_Std_Do_term___u2227_u2091___00__closed__2;
                leanh::lean_inc(v___x_1804_);
                v___x_1807_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1807_, 0, v___x_1804_);
                leanh::lean_ctor_set(v___x_1807_, 1, v___x_1806_);
                v___x_1808_ = l_Lean_Syntax_node3(
                    v___x_1804_,
                    v___x_1805_,
                    v___x_1800_,
                    v___x_1807_,
                    v___x_1801_,
                );
                v___x_1809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                leanh::lean_ctor_set(v___x_1809_, 1, v_a_1783_);
                return v___x_1809_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v_a_1811_: *mut leanh::LeanObject,
    mut v_a_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(
        v_x_1810_, v_a_1811_, v_a_1812_,
    );
    leanh::lean_dec(v_a_1811_);
    return v_res_1813_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp___lam__0(
    mut v_a_1814_: *mut leanh::LeanObject,
    mut v_fst_1815_: *mut leanh::LeanObject,
    mut v_fst_1816_: *mut leanh::LeanObject,
    mut v_e_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = l_Std_Do_PostShape_args(v_a_1814_);
    leanh::lean_inc(v_e_1817_);
    v___x_1819_ = leanh::lean_apply_1(v_fst_1815_, v_e_1817_);
    v___x_1820_ = leanh::lean_apply_1(v_fst_1816_, v_e_1817_);
    v___x_1821_ = l_Std_Do_SPred_imp(v___x_1818_, v___x_1819_, v___x_1820_);
    return v___x_1821_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp___lam__0___boxed(
    mut v_a_1822_: *mut leanh::LeanObject,
    mut v_fst_1823_: *mut leanh::LeanObject,
    mut v_fst_1824_: *mut leanh::LeanObject,
    mut v_e_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1826_ = l_Std_Do_ExceptConds_imp___lam__0(v_a_1822_, v_fst_1823_, v_fst_1824_, v_e_1825_);
    leanh::lean_dec(v_a_1822_);
    return v_res_1826_;
}
pub unsafe fn l_Std_Do_ExceptConds_imp(
    mut v_ps_1827_: *mut leanh::LeanObject,
    mut v_x_1828_: *mut leanh::LeanObject,
    mut v_y_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___f_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_ps_1827_) {
                0 => {
                    leanh::lean_dec(v_y_1829_);
                    leanh::lean_dec(v_x_1828_);
                    v___x_1830_ = leanh::lean_box(0);
                    return v___x_1830_;
                }
                1 => {
                    v_a_1831_ = leanh::lean_ctor_get(v_ps_1827_, 0);
                    leanh::lean_inc(v_a_1831_);
                    leanh::lean_dec_ref_known(v_ps_1827_, 1);
                    v_ps_1827_ = v_a_1831_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_1833_ = leanh::lean_ctor_get(v_ps_1827_, 0);
                    leanh::lean_inc(v_a_1833_);
                    leanh::lean_dec_ref_known(v_ps_1827_, 1);
                    v_fst_1834_ = leanh::lean_ctor_get(v_x_1828_, 0);
                    leanh::lean_inc(v_fst_1834_);
                    v_snd_1835_ = leanh::lean_ctor_get(v_x_1828_, 1);
                    leanh::lean_inc(v_snd_1835_);
                    leanh::lean_dec(v_x_1828_);
                    v_fst_1836_ = leanh::lean_ctor_get(v_y_1829_, 0);
                    v_snd_1837_ = leanh::lean_ctor_get(v_y_1829_, 1);
                    v_isSharedCheck_1846_ = (!leanh::lean_is_exclusive(v_y_1829_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v___x_1839_ = v_y_1829_;
                        v_isShared_1840_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1837_);
                        leanh::lean_inc(v_fst_1836_);
                        leanh::lean_dec(v_y_1829_);
                        v___x_1839_ = leanh::lean_box(0);
                        v_isShared_1840_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                leanh::lean_inc(v_a_1833_);
                v___f_1841_ = leanh::lean_alloc_closure(
                    l_Std_Do_ExceptConds_imp___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1841_, 0, v_a_1833_);
                leanh::lean_closure_set(v___f_1841_, 1, v_fst_1834_);
                leanh::lean_closure_set(v___f_1841_, 2, v_fst_1836_);
                v___x_1842_ = l_Std_Do_ExceptConds_imp(v_a_1833_, v_snd_1835_, v_snd_1837_);
                if v_isShared_1840_ == 0 {
                    leanh::lean_ctor_set(v___x_1839_, 1, v___x_1842_);
                    leanh::lean_ctor_set(v___x_1839_, 0, v___f_1841_);
                    v___x_1844_ = v___x_1839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___f_1841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
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
-> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0;
    v___x_1867_ = l_String_toRawSubstring_x27(v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(
    mut v_x_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
    mut v_a_1885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: u8 = 0;
    v___x_1886_ = l_Std_Do_term___u2192_u2091___00__closed__1;
    leanh::lean_inc(v_x_1883_);
    v___x_1887_ = l_Lean_Syntax_isOfKind(v_x_1883_, v___x_1886_);
    if v___x_1887_ == 0 {
        let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1883_);
        v___x_1888_ = leanh::lean_box(1);
        v___x_1889_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1889_, 0, v___x_1888_);
        leanh::lean_ctor_set(v___x_1889_, 1, v_a_1885_);
        return v___x_1889_;
    } else {
        let mut v_quotContext_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: u8 = 0;
        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1890_ = leanh::lean_ctor_get(v_a_1884_, 1);
        v_currMacroScope_1891_ = leanh::lean_ctor_get(v_a_1884_, 2);
        v_ref_1892_ = leanh::lean_ctor_get(v_a_1884_, 5);
        v___x_1893_ = leanh::lean_unsigned_to_nat(0);
        v___x_1894_ = l_Lean_Syntax_getArg(v_x_1883_, v___x_1893_);
        v___x_1895_ = leanh::lean_unsigned_to_nat(2);
        v___x_1896_ = l_Lean_Syntax_getArg(v_x_1883_, v___x_1895_);
        leanh::lean_dec(v_x_1883_);
        v___x_1897_ = 0;
        v___x_1898_ = l_Lean_SourceInfo_fromRef(v_ref_1892_, v___x_1897_);
        v___x_1899_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_1900_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1);
        v___x_1901_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3;
        leanh::lean_inc(v_currMacroScope_1891_);
        leanh::lean_inc(v_quotContext_1890_);
        v___x_1902_ =
            l_Lean_addMacroScope(v_quotContext_1890_, v___x_1901_, v_currMacroScope_1891_);
        v___x_1903_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6;
        leanh::lean_inc_n(v___x_1898_, 2);
        v___x_1904_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1904_, 0, v___x_1898_);
        leanh::lean_ctor_set(v___x_1904_, 1, v___x_1900_);
        leanh::lean_ctor_set(v___x_1904_, 2, v___x_1902_);
        leanh::lean_ctor_set(v___x_1904_, 3, v___x_1903_);
        v___x_1905_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_1906_ = l_Lean_Syntax_node2(v___x_1898_, v___x_1905_, v___x_1894_, v___x_1896_);
        v___x_1907_ = l_Lean_Syntax_node2(v___x_1898_, v___x_1899_, v___x_1904_, v___x_1906_);
        v___x_1908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
        leanh::lean_ctor_set(v___x_1908_, 1, v_a_1885_);
        return v___x_1908_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___boxed(
    mut v_x_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1912_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(
            v_x_1909_, v_a_1910_, v_a_1911_,
        );
    leanh::lean_dec_ref(v_a_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(
    mut v_x_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
    mut v_a_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    v___x_1916_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_1913_);
    v___x_1917_ = l_Lean_Syntax_isOfKind(v_x_1913_, v___x_1916_);
    if v___x_1917_ == 0 {
        let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1913_);
        v___x_1918_ = leanh::lean_box(0);
        v___x_1919_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1919_, 0, v___x_1918_);
        leanh::lean_ctor_set(v___x_1919_, 1, v_a_1915_);
        return v___x_1919_;
    } else {
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: u8 = 0;
        v___x_1920_ = leanh::lean_unsigned_to_nat(0);
        v___x_1921_ = l_Lean_Syntax_getArg(v_x_1913_, v___x_1920_);
        v___x_1922_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_1921_);
        v___x_1923_ = l_Lean_Syntax_isOfKind(v___x_1921_, v___x_1922_);
        if v___x_1923_ == 0 {
            let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1921_);
            leanh::lean_dec(v_x_1913_);
            v___x_1924_ = leanh::lean_box(0);
            v___x_1925_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
            leanh::lean_ctor_set(v___x_1925_, 1, v_a_1915_);
            return v___x_1925_;
        } else {
            let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1929_: u8 = 0;
            v___x_1926_ = leanh::lean_unsigned_to_nat(1);
            v___x_1927_ = l_Lean_Syntax_getArg(v_x_1913_, v___x_1926_);
            leanh::lean_dec(v_x_1913_);
            v___x_1928_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_1927_);
            v___x_1929_ = l_Lean_Syntax_matchesNull(v___x_1927_, v___x_1928_);
            if v___x_1929_ == 0 {
                let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1927_);
                leanh::lean_dec(v___x_1921_);
                v___x_1930_ = leanh::lean_box(0);
                v___x_1931_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1931_, 0, v___x_1930_);
                leanh::lean_ctor_set(v___x_1931_, 1, v_a_1915_);
                return v___x_1931_;
            } else {
                let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1935_: u8 = 0;
                let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1932_ = l_Lean_Syntax_getArg(v___x_1927_, v___x_1920_);
                v___x_1933_ = l_Lean_Syntax_getArg(v___x_1927_, v___x_1926_);
                leanh::lean_dec(v___x_1927_);
                v_ref_1934_ = l_Lean_replaceRef(v___x_1921_, v_a_1914_);
                leanh::lean_dec(v___x_1921_);
                v___x_1935_ = 0;
                v___x_1936_ = l_Lean_SourceInfo_fromRef(v_ref_1934_, v___x_1935_);
                leanh::lean_dec(v_ref_1934_);
                v___x_1937_ = l_Std_Do_term___u2192_u2091___00__closed__1;
                v___x_1938_ = l_Std_Do_term___u2192_u2091___00__closed__2;
                leanh::lean_inc(v___x_1936_);
                v___x_1939_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1939_, 0, v___x_1936_);
                leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
                v___x_1940_ = l_Lean_Syntax_node3(
                    v___x_1936_,
                    v___x_1937_,
                    v___x_1932_,
                    v___x_1939_,
                    v___x_1933_,
                );
                v___x_1941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1941_, 0, v___x_1940_);
                leanh::lean_ctor_set(v___x_1941_, 1, v_a_1915_);
                return v___x_1941_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(
    mut v_x_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(
        v_x_1942_, v_a_1943_, v_a_1944_,
    );
    leanh::lean_dec(v_a_1943_);
    return v_res_1945_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_2015_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14;
    v___x_2018_ = l_String_toRawSubstring_x27(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(
    mut v_x_2035_: *mut leanh::LeanObject,
    mut v_a_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    v___x_2038_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1;
    leanh::lean_inc(v_x_2035_);
    v___x_2039_ = l_Lean_Syntax_isOfKind(v_x_2035_, v___x_2038_);
    if v___x_2039_ == 0 {
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2035_);
        v___x_2040_ = leanh::lean_box(1);
        v___x_2041_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2041_, 0, v___x_2040_);
        leanh::lean_ctor_set(v___x_2041_, 1, v_a_2037_);
        return v___x_2041_;
    } else {
        let mut v_quotContext_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: u8 = 0;
        let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2042_ = leanh::lean_ctor_get(v_a_2036_, 1);
        v_currMacroScope_2043_ = leanh::lean_ctor_get(v_a_2036_, 2);
        v_ref_2044_ = leanh::lean_ctor_get(v_a_2036_, 5);
        v___x_2045_ = leanh::lean_unsigned_to_nat(1);
        v___x_2046_ = l_Lean_Syntax_getArg(v_x_2035_, v___x_2045_);
        leanh::lean_dec(v_x_2035_);
        v___x_2047_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5;
        v___x_2048_ = l_Lean_Syntax_getArgs(v___x_2046_);
        leanh::lean_dec(v___x_2046_);
        v___x_2049_ = 0;
        v___x_2050_ = l_Lean_SourceInfo_fromRef(v_ref_2044_, v___x_2049_);
        v___x_2051_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2052_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        leanh::lean_inc_n(v___x_2050_, 12);
        v___x_2053_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2053_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2053_, 1, v___x_2052_);
        v___x_2054_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2055_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2056_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2057_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2058_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2059_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2059_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2059_, 1, v___x_2057_);
        v___x_2060_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11;
        v___x_2061_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12;
        v___x_2062_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2062_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2062_, 1, v___x_2061_);
        v___x_2063_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v___x_2064_ = l_Array_append___redArg(v___x_2063_, v___x_2048_);
        leanh::lean_dec_ref(v___x_2048_);
        v___x_2065_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2065_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2065_, 1, v___x_2047_);
        v___x_2066_ = lean_array_push(v___x_2064_, v___x_2065_);
        v___x_2067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15);
        v___x_2068_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18;
        leanh::lean_inc(v_currMacroScope_2043_);
        leanh::lean_inc(v_quotContext_2042_);
        v___x_2069_ =
            l_Lean_addMacroScope(v_quotContext_2042_, v___x_2068_, v_currMacroScope_2043_);
        v___x_2070_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22;
        v___x_2071_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2071_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2071_, 1, v___x_2067_);
        leanh::lean_ctor_set(v___x_2071_, 2, v___x_2069_);
        leanh::lean_ctor_set(v___x_2071_, 3, v___x_2070_);
        v___x_2072_ = lean_array_push(v___x_2066_, v___x_2071_);
        v___x_2073_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2073_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2073_, 1, v___x_2056_);
        leanh::lean_ctor_set(v___x_2073_, 2, v___x_2072_);
        v___x_2074_ = l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10;
        v___x_2075_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2075_, 0, v___x_2050_);
        leanh::lean_ctor_set(v___x_2075_, 1, v___x_2074_);
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
        v___x_2082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
        leanh::lean_ctor_set(v___x_2082_, 1, v_a_2037_);
        return v___x_2082_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___boxed(
    mut v_x_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
    mut v_a_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(v_x_2083_, v_a_2084_, v_a_2085_);
    leanh::lean_dec_ref(v_a_2084_);
    return v_res_2086_;
}
pub unsafe fn l_Std_Do_PostCond_noThrow___redArg(
    mut v_ps_2087_: *mut leanh::LeanObject,
    mut v_p_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2087_);
    v___x_2090_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2090_, 0, v_p_2088_);
    leanh::lean_ctor_set(v___x_2090_, 1, v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l_Std_Do_PostCond_noThrow(
    mut v_00_u03b1_2091_: *mut leanh::LeanObject,
    mut v_ps_2092_: *mut leanh::LeanObject,
    mut v_p_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2092_);
    v___x_2095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2095_, 0, v_p_2093_);
    leanh::lean_ctor_set(v___x_2095_, 1, v___x_2094_);
    return v___x_2095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(
    mut v_sz_2148_: usize,
    mut v_i_2149_: usize,
    mut v_bs_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2151_: u8 = 0;
    let mut v_v_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: usize = 0;
    let mut v___x_2156_: usize = 0;
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2151_ = lean_usize_dec_lt(v_i_2149_, v_sz_2148_);
                if v___x_2151_ == 0 {
                    return v_bs_2150_;
                } else {
                    v_v_2152_ = lean_array_uget(v_bs_2150_, v_i_2149_);
                    v___x_2153_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_2159_: *mut leanh::LeanObject,
    mut v_i_2160_: *mut leanh::LeanObject,
    mut v_bs_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2162_: usize = 0;
    let mut v_i_boxed_2163_: usize = 0;
    let mut v_res_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2162_ = leanh::lean_unbox_usize(v_sz_2159_);
    leanh::lean_dec(v_sz_2159_);
    v_i_boxed_2163_ = leanh::lean_unbox_usize(v_i_2160_);
    leanh::lean_dec(v_i_2160_);
    v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_boxed_2162_, v_i_boxed_2163_, v_bs_2161_);
    return v_res_2164_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0;
    v___x_2167_ = l_String_toRawSubstring_x27(v___x_2166_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15;
    v___x_2202_ = l_String_toRawSubstring_x27(v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(
    mut v_x_2231_: *mut leanh::LeanObject,
    mut v_a_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    v___x_2234_ = l_Std_Do_term___u21d3___x3d_x3e___00__closed__1;
    leanh::lean_inc(v_x_2231_);
    v___x_2235_ = l_Lean_Syntax_isOfKind(v_x_2231_, v___x_2234_);
    if v___x_2235_ == 0 {
        let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2231_);
        v___x_2236_ = leanh::lean_box(1);
        v___x_2237_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
        leanh::lean_ctor_set(v___x_2237_, 1, v_a_2233_);
        return v___x_2237_;
    } else {
        let mut v_quotContext_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: u8 = 0;
        let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2280_: usize = 0;
        let mut v___x_2281_: usize = 0;
        let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2238_ = leanh::lean_ctor_get(v_a_2232_, 1);
        v_currMacroScope_2239_ = leanh::lean_ctor_get(v_a_2232_, 2);
        v_ref_2240_ = leanh::lean_ctor_get(v_a_2232_, 5);
        v___x_2241_ = leanh::lean_unsigned_to_nat(2);
        v___x_2242_ = l_Lean_Syntax_getArg(v_x_2231_, v___x_2241_);
        v___x_2243_ = leanh::lean_unsigned_to_nat(4);
        v___x_2244_ = l_Lean_Syntax_getArg(v_x_2231_, v___x_2243_);
        leanh::lean_dec(v_x_2231_);
        v_xs_2245_ = l_Lean_Syntax_getArgs(v___x_2242_);
        leanh::lean_dec(v___x_2242_);
        v___x_2246_ = 0;
        v___x_2247_ = l_Lean_SourceInfo_fromRef(v_ref_2240_, v___x_2246_);
        v___x_2248_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1);
        v___x_2250_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4;
        leanh::lean_inc_n(v_currMacroScope_2239_, 2);
        leanh::lean_inc_n(v_quotContext_2238_, 2);
        v___x_2251_ =
            l_Lean_addMacroScope(v_quotContext_2238_, v___x_2250_, v_currMacroScope_2239_);
        v___x_2252_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7;
        leanh::lean_inc_n(v___x_2247_, 23);
        v___x_2253_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2253_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2253_, 1, v___x_2249_);
        leanh::lean_ctor_set(v___x_2253_, 2, v___x_2251_);
        leanh::lean_ctor_set(v___x_2253_, 3, v___x_2252_);
        v___x_2254_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2255_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9;
        v___x_2256_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11;
        v___x_2257_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12;
        v___x_2258_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2258_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
        v___x_2259_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14;
        v___x_2260_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
        v___x_2261_ = leanh::lean_box(0);
        v___x_2262_ =
            l_Lean_addMacroScope(v_quotContext_2238_, v___x_2261_, v_currMacroScope_2239_);
        v___x_2263_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19;
        v___x_2264_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2264_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2264_, 1, v___x_2260_);
        leanh::lean_ctor_set(v___x_2264_, 2, v___x_2262_);
        leanh::lean_ctor_set(v___x_2264_, 3, v___x_2263_);
        v___x_2265_ = l_Lean_Syntax_node1(v___x_2247_, v___x_2259_, v___x_2264_);
        v___x_2266_ = l_Lean_Syntax_node2(v___x_2247_, v___x_2256_, v___x_2258_, v___x_2265_);
        v___x_2267_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2268_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        v___x_2269_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2269_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
        v___x_2270_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2271_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2272_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2273_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2274_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2274_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2274_, 1, v___x_2272_);
        v___x_2275_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20;
        v___x_2276_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21;
        v___x_2277_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2277_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2277_, 1, v___x_2275_);
        v___x_2278_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23;
        v___x_2279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v_sz_2280_ = lean_array_size(v_xs_2245_);
        v___x_2281_ = 0usize;
        v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_2280_, v___x_2281_, v_xs_2245_);
        v___x_2283_ = l_Array_append___redArg(v___x_2279_, v___x_2282_);
        leanh::lean_dec_ref(v___x_2282_);
        v___x_2284_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2284_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2284_, 1, v___x_2254_);
        leanh::lean_ctor_set(v___x_2284_, 2, v___x_2283_);
        v___x_2285_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2285_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2285_, 1, v___x_2254_);
        leanh::lean_ctor_set(v___x_2285_, 2, v___x_2279_);
        v___x_2286_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24;
        v___x_2287_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2287_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2287_, 1, v___x_2286_);
        v___x_2288_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26;
        v___x_2289_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27;
        v___x_2290_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2290_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        v___x_2291_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28;
        v___x_2292_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2292_, 0, v___x_2247_);
        leanh::lean_ctor_set(v___x_2292_, 1, v___x_2291_);
        leanh::lean_inc_ref(v___x_2292_);
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
        v___x_2304_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2304_, 0, v___x_2303_);
        leanh::lean_ctor_set(v___x_2304_, 1, v_a_2233_);
        return v___x_2304_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___boxed(
    mut v_x_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v_a_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2308_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(
            v_x_2305_, v_a_2306_, v_a_2307_,
        );
    leanh::lean_dec_ref(v_a_2306_);
    return v_res_2308_;
}
pub unsafe fn l_Std_Do_PostCond_mayThrow___redArg(
    mut v_ps_2309_: *mut leanh::LeanObject,
    mut v_p_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2309_);
    v___x_2312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2312_, 0, v_p_2310_);
    leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn l_Std_Do_PostCond_mayThrow(
    mut v_00_u03b1_2313_: *mut leanh::LeanObject,
    mut v_ps_2314_: *mut leanh::LeanObject,
    mut v_p_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2314_);
    v___x_2317_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2317_, 0, v_p_2315_);
    leanh::lean_ctor_set(v___x_2317_, 1, v___x_2316_);
    return v___x_2317_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0;
    v___x_2349_ = l_String_toRawSubstring_x27(v___x_2348_);
    return v___x_2349_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(
    mut v_x_2365_: *mut leanh::LeanObject,
    mut v_a_2366_: *mut leanh::LeanObject,
    mut v_a_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    v___x_2368_ = l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1;
    leanh::lean_inc(v_x_2365_);
    v___x_2369_ = l_Lean_Syntax_isOfKind(v_x_2365_, v___x_2368_);
    if v___x_2369_ == 0 {
        let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2365_);
        v___x_2370_ = leanh::lean_box(1);
        v___x_2371_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
        leanh::lean_ctor_set(v___x_2371_, 1, v_a_2367_);
        return v___x_2371_;
    } else {
        let mut v_quotContext_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2380_: u8 = 0;
        let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2414_: usize = 0;
        let mut v___x_2415_: usize = 0;
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
        v_quotContext_2372_ = leanh::lean_ctor_get(v_a_2366_, 1);
        v_currMacroScope_2373_ = leanh::lean_ctor_get(v_a_2366_, 2);
        v_ref_2374_ = leanh::lean_ctor_get(v_a_2366_, 5);
        v___x_2375_ = leanh::lean_unsigned_to_nat(2);
        v___x_2376_ = l_Lean_Syntax_getArg(v_x_2365_, v___x_2375_);
        v___x_2377_ = leanh::lean_unsigned_to_nat(4);
        v___x_2378_ = l_Lean_Syntax_getArg(v_x_2365_, v___x_2377_);
        leanh::lean_dec(v_x_2365_);
        v_xs_2379_ = l_Lean_Syntax_getArgs(v___x_2376_);
        leanh::lean_dec(v___x_2376_);
        v___x_2380_ = 0;
        v___x_2381_ = l_Lean_SourceInfo_fromRef(v_ref_2374_, v___x_2380_);
        v___x_2382_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2383_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1);
        v___x_2384_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3;
        leanh::lean_inc_n(v_currMacroScope_2373_, 2);
        leanh::lean_inc_n(v_quotContext_2372_, 2);
        v___x_2385_ =
            l_Lean_addMacroScope(v_quotContext_2372_, v___x_2384_, v_currMacroScope_2373_);
        v___x_2386_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6;
        leanh::lean_inc_n(v___x_2381_, 23);
        v___x_2387_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2387_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2387_, 1, v___x_2383_);
        leanh::lean_ctor_set(v___x_2387_, 2, v___x_2385_);
        leanh::lean_ctor_set(v___x_2387_, 3, v___x_2386_);
        v___x_2388_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2389_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9;
        v___x_2390_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11;
        v___x_2391_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12;
        v___x_2392_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2392_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2392_, 1, v___x_2391_);
        v___x_2393_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14;
        v___x_2394_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
        v___x_2395_ = leanh::lean_box(0);
        v___x_2396_ =
            l_Lean_addMacroScope(v_quotContext_2372_, v___x_2395_, v_currMacroScope_2373_);
        v___x_2397_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19;
        v___x_2398_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2398_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2398_, 1, v___x_2394_);
        leanh::lean_ctor_set(v___x_2398_, 2, v___x_2396_);
        leanh::lean_ctor_set(v___x_2398_, 3, v___x_2397_);
        v___x_2399_ = l_Lean_Syntax_node1(v___x_2381_, v___x_2393_, v___x_2398_);
        v___x_2400_ = l_Lean_Syntax_node2(v___x_2381_, v___x_2390_, v___x_2392_, v___x_2399_);
        v___x_2401_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1;
        v___x_2402_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2;
        v___x_2403_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2403_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2403_, 1, v___x_2402_);
        v___x_2404_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5;
        v___x_2405_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7;
        v___x_2406_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8;
        v___x_2407_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9;
        v___x_2408_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2408_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2408_, 1, v___x_2406_);
        v___x_2409_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20;
        v___x_2410_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21;
        v___x_2411_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2411_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2411_, 1, v___x_2409_);
        v___x_2412_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23;
        v___x_2413_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
        v_sz_2414_ = lean_array_size(v_xs_2379_);
        v___x_2415_ = 0usize;
        v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_2414_, v___x_2415_, v_xs_2379_);
        v___x_2417_ = l_Array_append___redArg(v___x_2413_, v___x_2416_);
        leanh::lean_dec_ref(v___x_2416_);
        v___x_2418_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2418_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2418_, 1, v___x_2388_);
        leanh::lean_ctor_set(v___x_2418_, 2, v___x_2417_);
        v___x_2419_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2419_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2419_, 1, v___x_2388_);
        leanh::lean_ctor_set(v___x_2419_, 2, v___x_2413_);
        v___x_2420_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24;
        v___x_2421_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2421_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2421_, 1, v___x_2420_);
        v___x_2422_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26;
        v___x_2423_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27;
        v___x_2424_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2424_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2424_, 1, v___x_2423_);
        v___x_2425_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28;
        v___x_2426_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2426_, 0, v___x_2381_);
        leanh::lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        leanh::lean_inc_ref(v___x_2426_);
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
        v___x_2438_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2438_, 0, v___x_2437_);
        leanh::lean_ctor_set(v___x_2438_, 1, v_a_2367_);
        return v___x_2438_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___boxed(
    mut v_x_2439_: *mut leanh::LeanObject,
    mut v_a_2440_: *mut leanh::LeanObject,
    mut v_a_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2442_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(
            v_x_2439_, v_a_2440_, v_a_2441_,
        );
    leanh::lean_dec_ref(v_a_2440_);
    return v_res_2442_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__0(
    mut v_x_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = leanh::lean_box(0);
    return v___x_2444_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(
    mut v_x_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Do_instInhabitedPostCond___redArg___lam__0(v_x_2445_);
    leanh::lean_dec(v_x_2445_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__1(
    mut v_ps_2447_: *mut leanh::LeanObject,
    mut v___f_2448_: *mut leanh::LeanObject,
    mut v_x_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Std_Do_PostShape_args(v_ps_2447_);
    v___x_2451_ = l_Std_Do_SVal_curry___redArg(v___x_2450_, leanh::lean_box(0));
    return v___x_2451_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(
    mut v_ps_2452_: *mut leanh::LeanObject,
    mut v___f_2453_: *mut leanh::LeanObject,
    mut v_x_2454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ =
        l_Std_Do_instInhabitedPostCond___redArg___lam__1(v_ps_2452_, v___f_2453_, v_x_2454_);
    leanh::lean_dec(v_x_2454_);
    leanh::lean_dec(v_ps_2452_);
    return v_res_2455_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond___redArg(
    mut v_ps_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ps_2456_);
    v___f_2457_ = leanh::lean_alloc_closure(
        l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2457_, 0, v_ps_2456_);
    leanh::lean_closure_set(v___f_2457_, 1, leanh::lean_box(0));
    v___x_2458_ = l_Std_Do_ExceptConds_const___redArg(v_ps_2456_);
    v___x_2459_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2459_, 0, v___f_2457_);
    leanh::lean_ctor_set(v___x_2459_, 1, v___x_2458_);
    return v___x_2459_;
}
pub unsafe fn l_Std_Do_instInhabitedPostCond(
    mut v_ps_2460_: *mut leanh::LeanObject,
    mut v_00_u03b1_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Std_Do_instInhabitedPostCond___redArg(v_ps_2460_);
    return v___x_2462_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0;
    v___x_2483_ = l_String_toRawSubstring_x27(v___x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(
    mut v_x_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    v___x_2501_ = l_Std_Do_term___u22a2_u209a___00__closed__1;
    leanh::lean_inc(v_x_2498_);
    v___x_2502_ = l_Lean_Syntax_isOfKind(v_x_2498_, v___x_2501_);
    if v___x_2502_ == 0 {
        let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2498_);
        v___x_2503_ = leanh::lean_box(1);
        v___x_2504_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
        leanh::lean_ctor_set(v___x_2504_, 1, v_a_2500_);
        return v___x_2504_;
    } else {
        let mut v_quotContext_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2512_: u8 = 0;
        let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2505_ = leanh::lean_ctor_get(v_a_2499_, 1);
        v_currMacroScope_2506_ = leanh::lean_ctor_get(v_a_2499_, 2);
        v_ref_2507_ = leanh::lean_ctor_get(v_a_2499_, 5);
        v___x_2508_ = leanh::lean_unsigned_to_nat(0);
        v___x_2509_ = l_Lean_Syntax_getArg(v_x_2498_, v___x_2508_);
        v___x_2510_ = leanh::lean_unsigned_to_nat(2);
        v___x_2511_ = l_Lean_Syntax_getArg(v_x_2498_, v___x_2510_);
        leanh::lean_dec(v_x_2498_);
        v___x_2512_ = 0;
        v___x_2513_ = l_Lean_SourceInfo_fromRef(v_ref_2507_, v___x_2512_);
        v___x_2514_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2515_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1);
        v___x_2516_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2;
        leanh::lean_inc(v_currMacroScope_2506_);
        leanh::lean_inc(v_quotContext_2505_);
        v___x_2517_ =
            l_Lean_addMacroScope(v_quotContext_2505_, v___x_2516_, v_currMacroScope_2506_);
        v___x_2518_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5;
        leanh::lean_inc_n(v___x_2513_, 2);
        v___x_2519_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2519_, 0, v___x_2513_);
        leanh::lean_ctor_set(v___x_2519_, 1, v___x_2515_);
        leanh::lean_ctor_set(v___x_2519_, 2, v___x_2517_);
        leanh::lean_ctor_set(v___x_2519_, 3, v___x_2518_);
        v___x_2520_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2521_ = l_Lean_Syntax_node2(v___x_2513_, v___x_2520_, v___x_2509_, v___x_2511_);
        v___x_2522_ = l_Lean_Syntax_node2(v___x_2513_, v___x_2514_, v___x_2519_, v___x_2521_);
        v___x_2523_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2523_, 0, v___x_2522_);
        leanh::lean_ctor_set(v___x_2523_, 1, v_a_2500_);
        return v___x_2523_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___boxed(
    mut v_x_2524_: *mut leanh::LeanObject,
    mut v_a_2525_: *mut leanh::LeanObject,
    mut v_a_2526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(
            v_x_2524_, v_a_2525_, v_a_2526_,
        );
    leanh::lean_dec_ref(v_a_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(
    mut v_x_2528_: *mut leanh::LeanObject,
    mut v_a_2529_: *mut leanh::LeanObject,
    mut v_a_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    v___x_2531_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_2528_);
    v___x_2532_ = l_Lean_Syntax_isOfKind(v_x_2528_, v___x_2531_);
    if v___x_2532_ == 0 {
        let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2528_);
        v___x_2533_ = leanh::lean_box(0);
        v___x_2534_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2534_, 0, v___x_2533_);
        leanh::lean_ctor_set(v___x_2534_, 1, v_a_2530_);
        return v___x_2534_;
    } else {
        let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2538_: u8 = 0;
        v___x_2535_ = leanh::lean_unsigned_to_nat(0);
        v___x_2536_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2535_);
        v___x_2537_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_2536_);
        v___x_2538_ = l_Lean_Syntax_isOfKind(v___x_2536_, v___x_2537_);
        if v___x_2538_ == 0 {
            let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2536_);
            leanh::lean_dec(v_x_2528_);
            v___x_2539_ = leanh::lean_box(0);
            v___x_2540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2540_, 0, v___x_2539_);
            leanh::lean_ctor_set(v___x_2540_, 1, v_a_2530_);
            return v___x_2540_;
        } else {
            let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2544_: u8 = 0;
            v___x_2541_ = leanh::lean_unsigned_to_nat(1);
            v___x_2542_ = l_Lean_Syntax_getArg(v_x_2528_, v___x_2541_);
            leanh::lean_dec(v_x_2528_);
            v___x_2543_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2542_);
            v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2542_, v___x_2543_);
            if v___x_2544_ == 0 {
                let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2542_);
                leanh::lean_dec(v___x_2536_);
                v___x_2545_ = leanh::lean_box(0);
                v___x_2546_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                leanh::lean_ctor_set(v___x_2546_, 1, v_a_2530_);
                return v___x_2546_;
            } else {
                let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2550_: u8 = 0;
                let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2547_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2535_);
                v___x_2548_ = l_Lean_Syntax_getArg(v___x_2542_, v___x_2541_);
                leanh::lean_dec(v___x_2542_);
                v_ref_2549_ = l_Lean_replaceRef(v___x_2536_, v_a_2529_);
                leanh::lean_dec(v___x_2536_);
                v___x_2550_ = 0;
                v___x_2551_ = l_Lean_SourceInfo_fromRef(v_ref_2549_, v___x_2550_);
                leanh::lean_dec(v_ref_2549_);
                v___x_2552_ = l_Std_Do_term___u22a2_u209a___00__closed__1;
                v___x_2553_ = l_Std_Do_term___u22a2_u209a___00__closed__2;
                leanh::lean_inc(v___x_2551_);
                v___x_2554_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2554_, 0, v___x_2551_);
                leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                v___x_2555_ = l_Lean_Syntax_node3(
                    v___x_2551_,
                    v___x_2552_,
                    v___x_2547_,
                    v___x_2554_,
                    v___x_2548_,
                );
                v___x_2556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2556_, 0, v___x_2555_);
                leanh::lean_ctor_set(v___x_2556_, 1, v_a_2530_);
                return v___x_2556_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(
    mut v_x_2557_: *mut leanh::LeanObject,
    mut v_a_2558_: *mut leanh::LeanObject,
    mut v_a_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(
        v_x_2557_, v_a_2558_, v_a_2559_,
    );
    leanh::lean_dec(v_a_2558_);
    return v_res_2560_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg___lam__0(
    mut v_ps_2561_: *mut leanh::LeanObject,
    mut v_fst_2562_: *mut leanh::LeanObject,
    mut v_fst_2563_: *mut leanh::LeanObject,
    mut v_a_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ = l_Std_Do_PostShape_args(v_ps_2561_);
    leanh::lean_inc(v_a_2564_);
    v___x_2566_ = leanh::lean_apply_1(v_fst_2562_, v_a_2564_);
    v___x_2567_ = leanh::lean_apply_1(v_fst_2563_, v_a_2564_);
    v___x_2568_ = l_Std_Do_SPred_and(v___x_2565_, v___x_2566_, v___x_2567_);
    return v___x_2568_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg___lam__0___boxed(
    mut v_ps_2569_: *mut leanh::LeanObject,
    mut v_fst_2570_: *mut leanh::LeanObject,
    mut v_fst_2571_: *mut leanh::LeanObject,
    mut v_a_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2573_ =
        l_Std_Do_PostCond_and___redArg___lam__0(v_ps_2569_, v_fst_2570_, v_fst_2571_, v_a_2572_);
    leanh::lean_dec(v_ps_2569_);
    return v_res_2573_;
}
pub unsafe fn l_Std_Do_PostCond_and___redArg(
    mut v_ps_2574_: *mut leanh::LeanObject,
    mut v_p_2575_: *mut leanh::LeanObject,
    mut v_q_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___f_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2577_ = leanh::lean_ctor_get(v_p_2575_, 0);
                leanh::lean_inc(v_fst_2577_);
                v_snd_2578_ = leanh::lean_ctor_get(v_p_2575_, 1);
                leanh::lean_inc(v_snd_2578_);
                leanh::lean_dec_ref(v_p_2575_);
                v_fst_2579_ = leanh::lean_ctor_get(v_q_2576_, 0);
                v_snd_2580_ = leanh::lean_ctor_get(v_q_2576_, 1);
                v_isSharedCheck_2589_ = (!leanh::lean_is_exclusive(v_q_2576_)) as u8;
                if v_isSharedCheck_2589_ == 0 {
                    v___x_2582_ = v_q_2576_;
                    v_isShared_2583_ = v_isSharedCheck_2589_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2580_);
                    leanh::lean_inc(v_fst_2579_);
                    leanh::lean_dec(v_q_2576_);
                    v___x_2582_ = leanh::lean_box(0);
                    v_isShared_2583_ = v_isSharedCheck_2589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ps_2574_);
                v___f_2584_ = leanh::lean_alloc_closure(
                    l_Std_Do_PostCond_and___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2584_, 0, v_ps_2574_);
                leanh::lean_closure_set(v___f_2584_, 1, v_fst_2577_);
                leanh::lean_closure_set(v___f_2584_, 2, v_fst_2579_);
                v___x_2585_ = l_Std_Do_ExceptConds_and(v_ps_2574_, v_snd_2578_, v_snd_2580_);
                if v_isShared_2583_ == 0 {
                    leanh::lean_ctor_set(v___x_2582_, 1, v___x_2585_);
                    leanh::lean_ctor_set(v___x_2582_, 0, v___f_2584_);
                    v___x_2587_ = v___x_2582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___f_2584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2588_, 1, v___x_2585_);
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
    mut v_00_u03b1_2590_: *mut leanh::LeanObject,
    mut v_ps_2591_: *mut leanh::LeanObject,
    mut v_p_2592_: *mut leanh::LeanObject,
    mut v_q_2593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___f_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2594_ = leanh::lean_ctor_get(v_p_2592_, 0);
                leanh::lean_inc(v_fst_2594_);
                v_snd_2595_ = leanh::lean_ctor_get(v_p_2592_, 1);
                leanh::lean_inc(v_snd_2595_);
                leanh::lean_dec_ref(v_p_2592_);
                v_fst_2596_ = leanh::lean_ctor_get(v_q_2593_, 0);
                v_snd_2597_ = leanh::lean_ctor_get(v_q_2593_, 1);
                v_isSharedCheck_2606_ = (!leanh::lean_is_exclusive(v_q_2593_)) as u8;
                if v_isSharedCheck_2606_ == 0 {
                    v___x_2599_ = v_q_2593_;
                    v_isShared_2600_ = v_isSharedCheck_2606_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2597_);
                    leanh::lean_inc(v_fst_2596_);
                    leanh::lean_dec(v_q_2593_);
                    v___x_2599_ = leanh::lean_box(0);
                    v_isShared_2600_ = v_isSharedCheck_2606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ps_2591_);
                v___f_2601_ = leanh::lean_alloc_closure(
                    l_Std_Do_PostCond_and___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2601_, 0, v_ps_2591_);
                leanh::lean_closure_set(v___f_2601_, 1, v_fst_2594_);
                leanh::lean_closure_set(v___f_2601_, 2, v_fst_2596_);
                v___x_2602_ = l_Std_Do_ExceptConds_and(v_ps_2591_, v_snd_2595_, v_snd_2597_);
                if v_isShared_2600_ == 0 {
                    leanh::lean_ctor_set(v___x_2599_, 1, v___x_2602_);
                    leanh::lean_ctor_set(v___x_2599_, 0, v___f_2601_);
                    v___x_2604_ = v___x_2599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___f_2601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2602_);
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
-> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0;
    v___x_2627_ = l_String_toRawSubstring_x27(v___x_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(
    mut v_x_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u8 = 0;
    v___x_2645_ = l_Std_Do_term___u2227_u209a___00__closed__1;
    leanh::lean_inc(v_x_2642_);
    v___x_2646_ = l_Lean_Syntax_isOfKind(v_x_2642_, v___x_2645_);
    if v___x_2646_ == 0 {
        let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2642_);
        v___x_2647_ = leanh::lean_box(1);
        v___x_2648_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2648_, 0, v___x_2647_);
        leanh::lean_ctor_set(v___x_2648_, 1, v_a_2644_);
        return v___x_2648_;
    } else {
        let mut v_quotContext_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2656_: u8 = 0;
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
        v_quotContext_2649_ = leanh::lean_ctor_get(v_a_2643_, 1);
        v_currMacroScope_2650_ = leanh::lean_ctor_get(v_a_2643_, 2);
        v_ref_2651_ = leanh::lean_ctor_get(v_a_2643_, 5);
        v___x_2652_ = leanh::lean_unsigned_to_nat(0);
        v___x_2653_ = l_Lean_Syntax_getArg(v_x_2642_, v___x_2652_);
        v___x_2654_ = leanh::lean_unsigned_to_nat(2);
        v___x_2655_ = l_Lean_Syntax_getArg(v_x_2642_, v___x_2654_);
        leanh::lean_dec(v_x_2642_);
        v___x_2656_ = 0;
        v___x_2657_ = l_Lean_SourceInfo_fromRef(v_ref_2651_, v___x_2656_);
        v___x_2658_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2659_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1);
        v___x_2660_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2;
        leanh::lean_inc(v_currMacroScope_2650_);
        leanh::lean_inc(v_quotContext_2649_);
        v___x_2661_ =
            l_Lean_addMacroScope(v_quotContext_2649_, v___x_2660_, v_currMacroScope_2650_);
        v___x_2662_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5;
        leanh::lean_inc_n(v___x_2657_, 2);
        v___x_2663_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2663_, 0, v___x_2657_);
        leanh::lean_ctor_set(v___x_2663_, 1, v___x_2659_);
        leanh::lean_ctor_set(v___x_2663_, 2, v___x_2661_);
        leanh::lean_ctor_set(v___x_2663_, 3, v___x_2662_);
        v___x_2664_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2665_ = l_Lean_Syntax_node2(v___x_2657_, v___x_2664_, v___x_2653_, v___x_2655_);
        v___x_2666_ = l_Lean_Syntax_node2(v___x_2657_, v___x_2658_, v___x_2663_, v___x_2665_);
        v___x_2667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2667_, 0, v___x_2666_);
        leanh::lean_ctor_set(v___x_2667_, 1, v_a_2644_);
        return v___x_2667_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___boxed(
    mut v_x_2668_: *mut leanh::LeanObject,
    mut v_a_2669_: *mut leanh::LeanObject,
    mut v_a_2670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2671_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(
            v_x_2668_, v_a_2669_, v_a_2670_,
        );
    leanh::lean_dec_ref(v_a_2669_);
    return v_res_2671_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(
    mut v_x_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    v___x_2675_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_2672_);
    v___x_2676_ = l_Lean_Syntax_isOfKind(v_x_2672_, v___x_2675_);
    if v___x_2676_ == 0 {
        let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2672_);
        v___x_2677_ = leanh::lean_box(0);
        v___x_2678_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2678_, 0, v___x_2677_);
        leanh::lean_ctor_set(v___x_2678_, 1, v_a_2674_);
        return v___x_2678_;
    } else {
        let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2682_: u8 = 0;
        v___x_2679_ = leanh::lean_unsigned_to_nat(0);
        v___x_2680_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2679_);
        v___x_2681_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_2680_);
        v___x_2682_ = l_Lean_Syntax_isOfKind(v___x_2680_, v___x_2681_);
        if v___x_2682_ == 0 {
            let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2680_);
            leanh::lean_dec(v_x_2672_);
            v___x_2683_ = leanh::lean_box(0);
            v___x_2684_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
            leanh::lean_ctor_set(v___x_2684_, 1, v_a_2674_);
            return v___x_2684_;
        } else {
            let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2688_: u8 = 0;
            v___x_2685_ = leanh::lean_unsigned_to_nat(1);
            v___x_2686_ = l_Lean_Syntax_getArg(v_x_2672_, v___x_2685_);
            leanh::lean_dec(v_x_2672_);
            v___x_2687_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2686_);
            v___x_2688_ = l_Lean_Syntax_matchesNull(v___x_2686_, v___x_2687_);
            if v___x_2688_ == 0 {
                let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2686_);
                leanh::lean_dec(v___x_2680_);
                v___x_2689_ = leanh::lean_box(0);
                v___x_2690_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2690_, 0, v___x_2689_);
                leanh::lean_ctor_set(v___x_2690_, 1, v_a_2674_);
                return v___x_2690_;
            } else {
                let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2694_: u8 = 0;
                let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2691_ = l_Lean_Syntax_getArg(v___x_2686_, v___x_2679_);
                v___x_2692_ = l_Lean_Syntax_getArg(v___x_2686_, v___x_2685_);
                leanh::lean_dec(v___x_2686_);
                v_ref_2693_ = l_Lean_replaceRef(v___x_2680_, v_a_2673_);
                leanh::lean_dec(v___x_2680_);
                v___x_2694_ = 0;
                v___x_2695_ = l_Lean_SourceInfo_fromRef(v_ref_2693_, v___x_2694_);
                leanh::lean_dec(v_ref_2693_);
                v___x_2696_ = l_Std_Do_term___u2227_u209a___00__closed__1;
                v___x_2697_ = l_Std_Do_term___u2227_u209a___00__closed__2;
                leanh::lean_inc(v___x_2695_);
                v___x_2698_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2698_, 0, v___x_2695_);
                leanh::lean_ctor_set(v___x_2698_, 1, v___x_2697_);
                v___x_2699_ = l_Lean_Syntax_node3(
                    v___x_2695_,
                    v___x_2696_,
                    v___x_2691_,
                    v___x_2698_,
                    v___x_2692_,
                );
                v___x_2700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
                leanh::lean_ctor_set(v___x_2700_, 1, v_a_2674_);
                return v___x_2700_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(
    mut v_x_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
    mut v_a_2703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2704_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(
        v_x_2701_, v_a_2702_, v_a_2703_,
    );
    leanh::lean_dec(v_a_2702_);
    return v_res_2704_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg___lam__0(
    mut v_ps_2705_: *mut leanh::LeanObject,
    mut v_fst_2706_: *mut leanh::LeanObject,
    mut v_fst_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ = l_Std_Do_PostShape_args(v_ps_2705_);
    leanh::lean_inc(v_a_2708_);
    v___x_2710_ = leanh::lean_apply_1(v_fst_2706_, v_a_2708_);
    v___x_2711_ = leanh::lean_apply_1(v_fst_2707_, v_a_2708_);
    v___x_2712_ = l_Std_Do_SPred_imp(v___x_2709_, v___x_2710_, v___x_2711_);
    return v___x_2712_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg___lam__0___boxed(
    mut v_ps_2713_: *mut leanh::LeanObject,
    mut v_fst_2714_: *mut leanh::LeanObject,
    mut v_fst_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2717_ =
        l_Std_Do_PostCond_imp___redArg___lam__0(v_ps_2713_, v_fst_2714_, v_fst_2715_, v_a_2716_);
    leanh::lean_dec(v_ps_2713_);
    return v_res_2717_;
}
pub unsafe fn l_Std_Do_PostCond_imp___redArg(
    mut v_ps_2718_: *mut leanh::LeanObject,
    mut v_p_2719_: *mut leanh::LeanObject,
    mut v_q_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___f_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2721_ = leanh::lean_ctor_get(v_p_2719_, 0);
                leanh::lean_inc(v_fst_2721_);
                v_snd_2722_ = leanh::lean_ctor_get(v_p_2719_, 1);
                leanh::lean_inc(v_snd_2722_);
                leanh::lean_dec_ref(v_p_2719_);
                v_fst_2723_ = leanh::lean_ctor_get(v_q_2720_, 0);
                v_snd_2724_ = leanh::lean_ctor_get(v_q_2720_, 1);
                v_isSharedCheck_2733_ = (!leanh::lean_is_exclusive(v_q_2720_)) as u8;
                if v_isSharedCheck_2733_ == 0 {
                    v___x_2726_ = v_q_2720_;
                    v_isShared_2727_ = v_isSharedCheck_2733_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2724_);
                    leanh::lean_inc(v_fst_2723_);
                    leanh::lean_dec(v_q_2720_);
                    v___x_2726_ = leanh::lean_box(0);
                    v_isShared_2727_ = v_isSharedCheck_2733_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ps_2718_);
                v___f_2728_ = leanh::lean_alloc_closure(
                    l_Std_Do_PostCond_imp___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2728_, 0, v_ps_2718_);
                leanh::lean_closure_set(v___f_2728_, 1, v_fst_2721_);
                leanh::lean_closure_set(v___f_2728_, 2, v_fst_2723_);
                v___x_2729_ = l_Std_Do_ExceptConds_imp(v_ps_2718_, v_snd_2722_, v_snd_2724_);
                if v_isShared_2727_ == 0 {
                    leanh::lean_ctor_set(v___x_2726_, 1, v___x_2729_);
                    leanh::lean_ctor_set(v___x_2726_, 0, v___f_2728_);
                    v___x_2731_ = v___x_2726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___f_2728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2729_);
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
    mut v_00_u03b1_2734_: *mut leanh::LeanObject,
    mut v_ps_2735_: *mut leanh::LeanObject,
    mut v_p_2736_: *mut leanh::LeanObject,
    mut v_q_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___f_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2738_ = leanh::lean_ctor_get(v_p_2736_, 0);
                leanh::lean_inc(v_fst_2738_);
                v_snd_2739_ = leanh::lean_ctor_get(v_p_2736_, 1);
                leanh::lean_inc(v_snd_2739_);
                leanh::lean_dec_ref(v_p_2736_);
                v_fst_2740_ = leanh::lean_ctor_get(v_q_2737_, 0);
                v_snd_2741_ = leanh::lean_ctor_get(v_q_2737_, 1);
                v_isSharedCheck_2750_ = (!leanh::lean_is_exclusive(v_q_2737_)) as u8;
                if v_isSharedCheck_2750_ == 0 {
                    v___x_2743_ = v_q_2737_;
                    v_isShared_2744_ = v_isSharedCheck_2750_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2741_);
                    leanh::lean_inc(v_fst_2740_);
                    leanh::lean_dec(v_q_2737_);
                    v___x_2743_ = leanh::lean_box(0);
                    v_isShared_2744_ = v_isSharedCheck_2750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ps_2735_);
                v___f_2745_ = leanh::lean_alloc_closure(
                    l_Std_Do_PostCond_imp___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2745_, 0, v_ps_2735_);
                leanh::lean_closure_set(v___f_2745_, 1, v_fst_2738_);
                leanh::lean_closure_set(v___f_2745_, 2, v_fst_2740_);
                v___x_2746_ = l_Std_Do_ExceptConds_imp(v_ps_2735_, v_snd_2739_, v_snd_2741_);
                if v_isShared_2744_ == 0 {
                    leanh::lean_ctor_set(v___x_2743_, 1, v___x_2746_);
                    leanh::lean_ctor_set(v___x_2743_, 0, v___f_2745_);
                    v___x_2748_ = v___x_2743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2749_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___f_2745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 1, v___x_2746_);
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
-> *mut leanh::LeanObject {
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0;
    v___x_2771_ = l_String_toRawSubstring_x27(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(
    mut v_x_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: u8 = 0;
    v___x_2789_ = l_Std_Do_term___u2192_u209a___00__closed__1;
    leanh::lean_inc(v_x_2786_);
    v___x_2790_ = l_Lean_Syntax_isOfKind(v_x_2786_, v___x_2789_);
    if v___x_2790_ == 0 {
        let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2786_);
        v___x_2791_ = leanh::lean_box(1);
        v___x_2792_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2792_, 0, v___x_2791_);
        leanh::lean_ctor_set(v___x_2792_, 1, v_a_2788_);
        return v___x_2792_;
    } else {
        let mut v_quotContext_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2800_: u8 = 0;
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
        v_quotContext_2793_ = leanh::lean_ctor_get(v_a_2787_, 1);
        v_currMacroScope_2794_ = leanh::lean_ctor_get(v_a_2787_, 2);
        v_ref_2795_ = leanh::lean_ctor_get(v_a_2787_, 5);
        v___x_2796_ = leanh::lean_unsigned_to_nat(0);
        v___x_2797_ = l_Lean_Syntax_getArg(v_x_2786_, v___x_2796_);
        v___x_2798_ = leanh::lean_unsigned_to_nat(2);
        v___x_2799_ = l_Lean_Syntax_getArg(v_x_2786_, v___x_2798_);
        leanh::lean_dec(v_x_2786_);
        v___x_2800_ = 0;
        v___x_2801_ = l_Lean_SourceInfo_fromRef(v_ref_2795_, v___x_2800_);
        v___x_2802_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
        v___x_2803_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once), _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1);
        v___x_2804_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2;
        leanh::lean_inc(v_currMacroScope_2794_);
        leanh::lean_inc(v_quotContext_2793_);
        v___x_2805_ =
            l_Lean_addMacroScope(v_quotContext_2793_, v___x_2804_, v_currMacroScope_2794_);
        v___x_2806_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5;
        leanh::lean_inc_n(v___x_2801_, 2);
        v___x_2807_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2807_, 0, v___x_2801_);
        leanh::lean_ctor_set(v___x_2807_, 1, v___x_2803_);
        leanh::lean_ctor_set(v___x_2807_, 2, v___x_2805_);
        leanh::lean_ctor_set(v___x_2807_, 3, v___x_2806_);
        v___x_2808_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16;
        v___x_2809_ = l_Lean_Syntax_node2(v___x_2801_, v___x_2808_, v___x_2797_, v___x_2799_);
        v___x_2810_ = l_Lean_Syntax_node2(v___x_2801_, v___x_2802_, v___x_2807_, v___x_2809_);
        v___x_2811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2811_, 0, v___x_2810_);
        leanh::lean_ctor_set(v___x_2811_, 1, v_a_2788_);
        return v___x_2811_;
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___boxed(
    mut v_x_2812_: *mut leanh::LeanObject,
    mut v_a_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2815_ =
        l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(
            v_x_2812_, v_a_2813_, v_a_2814_,
        );
    leanh::lean_dec_ref(v_a_2813_);
    return v_res_2815_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(
    mut v_x_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_a_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    v___x_2819_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4;
    leanh::lean_inc(v_x_2816_);
    v___x_2820_ = l_Lean_Syntax_isOfKind(v_x_2816_, v___x_2819_);
    if v___x_2820_ == 0 {
        let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2816_);
        v___x_2821_ = leanh::lean_box(0);
        v___x_2822_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2822_, 0, v___x_2821_);
        leanh::lean_ctor_set(v___x_2822_, 1, v_a_2818_);
        return v___x_2822_;
    } else {
        let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2826_: u8 = 0;
        v___x_2823_ = leanh::lean_unsigned_to_nat(0);
        v___x_2824_ = l_Lean_Syntax_getArg(v_x_2816_, v___x_2823_);
        v___x_2825_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1;
        leanh::lean_inc(v___x_2824_);
        v___x_2826_ = l_Lean_Syntax_isOfKind(v___x_2824_, v___x_2825_);
        if v___x_2826_ == 0 {
            let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2824_);
            leanh::lean_dec(v_x_2816_);
            v___x_2827_ = leanh::lean_box(0);
            v___x_2828_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2828_, 0, v___x_2827_);
            leanh::lean_ctor_set(v___x_2828_, 1, v_a_2818_);
            return v___x_2828_;
        } else {
            let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2832_: u8 = 0;
            v___x_2829_ = leanh::lean_unsigned_to_nat(1);
            v___x_2830_ = l_Lean_Syntax_getArg(v_x_2816_, v___x_2829_);
            leanh::lean_dec(v_x_2816_);
            v___x_2831_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_2830_);
            v___x_2832_ = l_Lean_Syntax_matchesNull(v___x_2830_, v___x_2831_);
            if v___x_2832_ == 0 {
                let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2830_);
                leanh::lean_dec(v___x_2824_);
                v___x_2833_ = leanh::lean_box(0);
                v___x_2834_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2834_, 0, v___x_2833_);
                leanh::lean_ctor_set(v___x_2834_, 1, v_a_2818_);
                return v___x_2834_;
            } else {
                let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2838_: u8 = 0;
                let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2835_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2823_);
                v___x_2836_ = l_Lean_Syntax_getArg(v___x_2830_, v___x_2829_);
                leanh::lean_dec(v___x_2830_);
                v_ref_2837_ = l_Lean_replaceRef(v___x_2824_, v_a_2817_);
                leanh::lean_dec(v___x_2824_);
                v___x_2838_ = 0;
                v___x_2839_ = l_Lean_SourceInfo_fromRef(v_ref_2837_, v___x_2838_);
                leanh::lean_dec(v_ref_2837_);
                v___x_2840_ = l_Std_Do_term___u2192_u209a___00__closed__1;
                v___x_2841_ = l_Std_Do_term___u2192_u209a___00__closed__2;
                leanh::lean_inc(v___x_2839_);
                v___x_2842_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2842_, 0, v___x_2839_);
                leanh::lean_ctor_set(v___x_2842_, 1, v___x_2841_);
                v___x_2843_ = l_Lean_Syntax_node3(
                    v___x_2839_,
                    v___x_2840_,
                    v___x_2835_,
                    v___x_2842_,
                    v___x_2836_,
                );
                v___x_2844_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2844_, 0, v___x_2843_);
                leanh::lean_ctor_set(v___x_2844_, 1, v_a_2818_);
                return v___x_2844_;
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(
    mut v_x_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(
        v_x_2845_, v_a_2846_, v_a_2847_,
    );
    leanh::lean_dec(v_a_2846_);
    return v_res_2848_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_PostCond(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_PostCond(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_PostCond(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_PostCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_PostCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_PostCond(builtin);
}
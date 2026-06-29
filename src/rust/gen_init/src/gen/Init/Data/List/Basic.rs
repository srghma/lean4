// Lean compiler output
// Module: Init.Data.List.Basic
// Imports: Init.Data.List.Notation Init.Data.Zero Init.Grind.Tactics Init.SimpLemmas Init.Data.Nat.Basic
use crate::ffi::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_mod, lean_nat_mul,
    lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::List::Notation::{
    initialize_Init_Data_List_Notation, runtime_initialize_Init_Data_List_Notation,
};
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Data::Zero::{
    initialize_Init_Data_Zero, runtime_initialize_Init_Data_Zero,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_Lean_replaceRef, l_List_foldl___redArg, l_List_length___redArg,
    l_List_lengthTR___redArg, l_List_map___redArg, l_String_toRawSubstring_x27,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
pub static l_List_lex___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_lex___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_List_lex___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_List_lex___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_List_lex___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_List_lex___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_List_lex___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_lex___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__10_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_List_lex___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14997215300048349804 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__14_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_lex___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__15_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_List_lex___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__15_value)
                as *mut crate::leanh::LeanObject,
            7932075773091973500 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__17_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_lex___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__17_value)
                as *mut crate::leanh::LeanObject,
            7306243862518720553 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__19_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_List_lex___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__22_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_List_lex___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__22_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__24_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
    };
static mut l_List_lex___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__33_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 60, 95, 0],
    };
static mut l_List_lex___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__34_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__33_value)
                as *mut crate::leanh::LeanObject,
            6883052497475924672 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__35_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 100, 111, 116, 0],
    };
static mut l_List_lex___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__35_value) as *mut crate::leanh::LeanObject;
static l_List_lex___auto__1___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__36_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__35_value)
                as *mut crate::leanh::LeanObject,
            6167508377434939095 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_List_lex___auto__1___closed__37_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [194, 183, 0],
    };
static mut l_List_lex___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__37_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__42_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__43_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [60, 0],
    };
static mut l_List_lex___auto__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__43_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__48_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__49_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_List_lex___auto__1___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__49_value) as *mut crate::leanh::LeanObject;
static mut l_List_lex___auto__1___closed__50_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__52_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__53_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__54_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__55_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__56_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__57_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__59_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__60_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_List_lex___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_instAppend___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_appendTR as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_List_instAppend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_partition___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_partition___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_partition___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_List_term___x3c_x2b___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [116, 101, 114, 109, 95, 60, 43, 95, 0],
    };
static mut l_List_term___x3c_x2b___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_List_term___x3c_x2b___00__closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x2b___00__closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            5032644207915418729 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_List_term___x3c_x2b___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 60, 43, 32, 0],
    };
static mut l_List_term___x3c_x2b___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_term___x3c_x2b___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__11_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_List_term___x3c_x2b__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 117, 98, 108, 105, 115, 116, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut crate::leanh::LeanObject,3971429882733148553 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut crate::leanh::LeanObject,13118543908479833671 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 95, 60, 43, 58, 95, 0],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x2b_x3a___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            11338394075872571116 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 43, 58, 32, 0],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_List_term___x3c_x2b_x3a__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 115, 80, 114, 101, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject,4340084101528514341 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject,11033310021417905675 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 95, 60, 58, 43, 95, 0],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x3a_x2b___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            3367210673871417624 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 58, 43, 32, 0],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_List_term___x3c_x3a_x2b__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 115, 83, 117, 102, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut crate::leanh::LeanObject,2296567635584722319 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut crate::leanh::LeanObject,12518011436897045665 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 58, 43, 58, 95, 0],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            5638408978683487334 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 58, 43, 58, 32, 0],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_List_term___x3c_x3a_x2b_x3a__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 115, 73, 110, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject,10897887609920352419 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut crate::leanh::LeanObject,9055159914511838349 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x7e___00__closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 126, 95, 0],
    };
static mut l_List_term___x7e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__0_value) as *mut crate::leanh::LeanObject;
static l_List_term___x7e___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_term___x7e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            17617384562182800008 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x7e___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 126, 32, 0],
    };
static mut l_List_term___x7e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x7e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_List_term___x7e___00__closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_List_term___x7e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x7e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_term___x7e___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_List_term___x7e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 101, 114, 109, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut crate::leanh::LeanObject,6725144291058853725 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut crate::leanh::LeanObject,6626821958560496499 as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(
    mut v_x_3488_: *mut crate::leanh::LeanObject,
    mut v_x_3489_: *mut crate::leanh::LeanObject,
    mut v_x_3490_: *mut crate::leanh::LeanObject,
    mut v_h__1_3491_: *mut crate::leanh::LeanObject,
    mut v_h__2_3492_: *mut crate::leanh::LeanObject,
    mut v_h__3_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3488_) == 0 {
        let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3492_);
        crate::leanh::lean_dec(v_h__1_3491_);
        v___x_3494_ = crate::leanh::lean_apply_2(v_h__3_3493_, v_x_3489_, v_x_3490_);
        return v___x_3494_;
    } else {
        let mut v_head_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_3498_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_3493_);
        v_head_3495_ = crate::leanh::lean_ctor_get(v_x_3488_, 0);
        crate::leanh::lean_inc(v_head_3495_);
        v_tail_3496_ = crate::leanh::lean_ctor_get(v_x_3488_, 1);
        crate::leanh::lean_inc(v_tail_3496_);
        crate::leanh::lean_dec_ref_known(v_x_3488_, 2);
        v_zero_3497_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_3498_ = lean_nat_dec_eq(v_x_3489_, v_zero_3497_);
        if v_isZero_3498_ == 1 {
            let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3492_);
            crate::leanh::lean_dec(v_x_3489_);
            v___x_3499_ =
                crate::leanh::lean_apply_3(v_h__1_3491_, v_head_3495_, v_tail_3496_, v_x_3490_);
            return v___x_3499_;
        } else {
            let mut v_one_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_3491_);
            v_one_3500_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_3501_ = lean_nat_sub(v_x_3489_, v_one_3500_);
            crate::leanh::lean_dec(v_x_3489_);
            v___x_3502_ = crate::leanh::lean_apply_4(
                v_h__2_3492_,
                v_head_3495_,
                v_tail_3496_,
                v_n_3501_,
                v_x_3490_,
            );
            return v___x_3502_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_set_match__1_splitter(
    mut v_00_u03b1_3503_: *mut crate::leanh::LeanObject,
    mut v_motive_3504_: *mut crate::leanh::LeanObject,
    mut v_x_3505_: *mut crate::leanh::LeanObject,
    mut v_x_3506_: *mut crate::leanh::LeanObject,
    mut v_x_3507_: *mut crate::leanh::LeanObject,
    mut v_h__1_3508_: *mut crate::leanh::LeanObject,
    mut v_h__2_3509_: *mut crate::leanh::LeanObject,
    mut v_h__3_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3505_) == 0 {
        let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3509_);
        crate::leanh::lean_dec(v_h__1_3508_);
        v___x_3511_ = crate::leanh::lean_apply_2(v_h__3_3510_, v_x_3506_, v_x_3507_);
        return v___x_3511_;
    } else {
        let mut v_head_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_3515_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_3510_);
        v_head_3512_ = crate::leanh::lean_ctor_get(v_x_3505_, 0);
        crate::leanh::lean_inc(v_head_3512_);
        v_tail_3513_ = crate::leanh::lean_ctor_get(v_x_3505_, 1);
        crate::leanh::lean_inc(v_tail_3513_);
        crate::leanh::lean_dec_ref_known(v_x_3505_, 2);
        v_zero_3514_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_3515_ = lean_nat_dec_eq(v_x_3506_, v_zero_3514_);
        if v_isZero_3515_ == 1 {
            let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3509_);
            crate::leanh::lean_dec(v_x_3506_);
            v___x_3516_ =
                crate::leanh::lean_apply_3(v_h__1_3508_, v_head_3512_, v_tail_3513_, v_x_3507_);
            return v___x_3516_;
        } else {
            let mut v_one_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_3508_);
            v_one_3517_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_3518_ = lean_nat_sub(v_x_3506_, v_one_3517_);
            crate::leanh::lean_dec(v_x_3506_);
            v___x_3519_ = crate::leanh::lean_apply_4(
                v_h__2_3509_,
                v_head_3512_,
                v_tail_3513_,
                v_n_3518_,
                v_x_3507_,
            );
            return v___x_3519_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter___redArg(
    mut v_x_3520_: *mut crate::leanh::LeanObject,
    mut v_x_3521_: *mut crate::leanh::LeanObject,
    mut v_h__1_3522_: *mut crate::leanh::LeanObject,
    mut v_h__2_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3520_) == 0 {
        let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3523_);
        v___x_3524_ = crate::leanh::lean_apply_1(v_h__1_3522_, v_x_3521_);
        return v___x_3524_;
    } else {
        let mut v_head_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3522_);
        v_head_3525_ = crate::leanh::lean_ctor_get(v_x_3520_, 0);
        crate::leanh::lean_inc(v_head_3525_);
        v_tail_3526_ = crate::leanh::lean_ctor_get(v_x_3520_, 1);
        crate::leanh::lean_inc(v_tail_3526_);
        crate::leanh::lean_dec_ref_known(v_x_3520_, 2);
        v___x_3527_ =
            crate::leanh::lean_apply_3(v_h__2_3523_, v_head_3525_, v_tail_3526_, v_x_3521_);
        return v___x_3527_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(
    mut v_00_u03b1_3528_: *mut crate::leanh::LeanObject,
    mut v_motive_3529_: *mut crate::leanh::LeanObject,
    mut v_x_3530_: *mut crate::leanh::LeanObject,
    mut v_x_3531_: *mut crate::leanh::LeanObject,
    mut v_h__1_3532_: *mut crate::leanh::LeanObject,
    mut v_h__2_3533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3530_) == 0 {
        let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_3533_);
        v___x_3534_ = crate::leanh::lean_apply_1(v_h__1_3532_, v_x_3531_);
        return v___x_3534_;
    } else {
        let mut v_head_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_3532_);
        v_head_3535_ = crate::leanh::lean_ctor_get(v_x_3530_, 0);
        crate::leanh::lean_inc(v_head_3535_);
        v_tail_3536_ = crate::leanh::lean_ctor_get(v_x_3530_, 1);
        crate::leanh::lean_inc(v_tail_3536_);
        crate::leanh::lean_dec_ref_known(v_x_3530_, 2);
        v___x_3537_ =
            crate::leanh::lean_apply_3(v_h__2_3533_, v_head_3535_, v_tail_3536_, v_x_3531_);
        return v___x_3537_;
    }
}
pub unsafe fn l_List_beq___redArg(
    mut v_inst_3538_: *mut crate::leanh::LeanObject,
    mut v_x_3539_: *mut crate::leanh::LeanObject,
    mut v_x_3540_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: u8 = 0;
    let mut v_head_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3539_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_3538_);
                    if crate::leanh::lean_obj_tag(v_x_3540_) == 0 {
                        v___x_3541_ = 1;
                        return v___x_3541_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3540_, 2);
                        v___x_3542_ = 0;
                        return v___x_3542_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3540_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_3539_, 2);
                        crate::leanh::lean_dec_ref(v_inst_3538_);
                        v___x_3543_ = 0;
                        return v___x_3543_;
                    } else {
                        v_head_3544_ = crate::leanh::lean_ctor_get(v_x_3539_, 0);
                        crate::leanh::lean_inc(v_head_3544_);
                        v_tail_3545_ = crate::leanh::lean_ctor_get(v_x_3539_, 1);
                        crate::leanh::lean_inc(v_tail_3545_);
                        crate::leanh::lean_dec_ref_known(v_x_3539_, 2);
                        v_head_3546_ = crate::leanh::lean_ctor_get(v_x_3540_, 0);
                        crate::leanh::lean_inc(v_head_3546_);
                        v_tail_3547_ = crate::leanh::lean_ctor_get(v_x_3540_, 1);
                        crate::leanh::lean_inc(v_tail_3547_);
                        crate::leanh::lean_dec_ref_known(v_x_3540_, 2);
                        crate::leanh::lean_inc_ref(v_inst_3538_);
                        v___x_3548_ =
                            crate::leanh::lean_apply_2(v_inst_3538_, v_head_3544_, v_head_3546_);
                        v___x_3549_ = (crate::leanh::lean_unbox(v___x_3548_) as u8);
                        if v___x_3549_ == 0 {
                            crate::leanh::lean_dec(v_tail_3547_);
                            crate::leanh::lean_dec(v_tail_3545_);
                            crate::leanh::lean_dec_ref(v_inst_3538_);
                            v___x_3550_ = (crate::leanh::lean_unbox(v___x_3548_) as u8);
                            return v___x_3550_;
                        } else {
                            v_x_3539_ = v_tail_3545_;
                            v_x_3540_ = v_tail_3547_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___redArg___boxed(
    mut v_inst_3552_: *mut crate::leanh::LeanObject,
    mut v_x_3553_: *mut crate::leanh::LeanObject,
    mut v_x_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3555_: u8 = 0;
    let mut v_r_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l_List_beq___redArg(v_inst_3552_, v_x_3553_, v_x_3554_);
    v_r_3556_ = crate::leanh::lean_box((v_res_3555_) as usize);
    return v_r_3556_;
}
pub unsafe fn l_List_beq(
    mut v_00_u03b1_3557_: *mut crate::leanh::LeanObject,
    mut v_inst_3558_: *mut crate::leanh::LeanObject,
    mut v_x_3559_: *mut crate::leanh::LeanObject,
    mut v_x_3560_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3561_: u8 = 0;
    v___x_3561_ = l_List_beq___redArg(v_inst_3558_, v_x_3559_, v_x_3560_);
    return v___x_3561_;
}
pub unsafe fn l_List_beq___boxed(
    mut v_00_u03b1_3562_: *mut crate::leanh::LeanObject,
    mut v_inst_3563_: *mut crate::leanh::LeanObject,
    mut v_x_3564_: *mut crate::leanh::LeanObject,
    mut v_x_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3566_: u8 = 0;
    let mut v_r_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3566_ = l_List_beq(v_00_u03b1_3562_, v_inst_3563_, v_x_3564_, v_x_3565_);
    v_r_3567_ = crate::leanh::lean_box((v_res_3566_) as usize);
    return v_r_3567_;
}
pub unsafe fn l_List_instBEq___redArg(
    mut v_inst_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ =
        crate::leanh::lean_alloc_closure(l_List_beq___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3569_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3569_, 1, v_inst_3568_);
    return v___x_3569_;
}
pub unsafe fn l_List_instBEq(
    mut v_00_u03b1_3570_: *mut crate::leanh::LeanObject,
    mut v_inst_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3572_ =
        crate::leanh::lean_alloc_closure(l_List_beq___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_3572_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3572_, 1, v_inst_3571_);
    return v___x_3572_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(
    mut v_x_3573_: *mut crate::leanh::LeanObject,
    mut v_x_3574_: *mut crate::leanh::LeanObject,
    mut v_h__1_3575_: *mut crate::leanh::LeanObject,
    mut v_h__2_3576_: *mut crate::leanh::LeanObject,
    mut v_h__3_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3573_) == 0 {
        crate::leanh::lean_dec(v_h__2_3576_);
        if crate::leanh::lean_obj_tag(v_x_3574_) == 0 {
            let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3577_);
            v___x_3578_ = crate::leanh::lean_box(0);
            v___x_3579_ = crate::leanh::lean_apply_1(v_h__1_3575_, v___x_3578_);
            return v___x_3579_;
        } else {
            let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_3575_);
            v___x_3580_ = crate::leanh::lean_apply_4(
                v_h__3_3577_,
                v_x_3573_,
                v_x_3574_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3580_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_3575_);
        if crate::leanh::lean_obj_tag(v_x_3574_) == 0 {
            let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3576_);
            v___x_3581_ = crate::leanh::lean_apply_4(
                v_h__3_3577_,
                v_x_3573_,
                v_x_3574_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3581_;
        } else {
            let mut v_head_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3577_);
            v_head_3582_ = crate::leanh::lean_ctor_get(v_x_3573_, 0);
            crate::leanh::lean_inc(v_head_3582_);
            v_tail_3583_ = crate::leanh::lean_ctor_get(v_x_3573_, 1);
            crate::leanh::lean_inc(v_tail_3583_);
            crate::leanh::lean_dec_ref_known(v_x_3573_, 2);
            v_head_3584_ = crate::leanh::lean_ctor_get(v_x_3574_, 0);
            crate::leanh::lean_inc(v_head_3584_);
            v_tail_3585_ = crate::leanh::lean_ctor_get(v_x_3574_, 1);
            crate::leanh::lean_inc(v_tail_3585_);
            crate::leanh::lean_dec_ref_known(v_x_3574_, 2);
            v___x_3586_ = crate::leanh::lean_apply_4(
                v_h__2_3576_,
                v_head_3582_,
                v_tail_3583_,
                v_head_3584_,
                v_tail_3585_,
            );
            return v___x_3586_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter(
    mut v_00_u03b1_3587_: *mut crate::leanh::LeanObject,
    mut v_motive_3588_: *mut crate::leanh::LeanObject,
    mut v_x_3589_: *mut crate::leanh::LeanObject,
    mut v_x_3590_: *mut crate::leanh::LeanObject,
    mut v_h__1_3591_: *mut crate::leanh::LeanObject,
    mut v_h__2_3592_: *mut crate::leanh::LeanObject,
    mut v_h__3_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3589_) == 0 {
        crate::leanh::lean_dec(v_h__2_3592_);
        if crate::leanh::lean_obj_tag(v_x_3590_) == 0 {
            let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3593_);
            v___x_3594_ = crate::leanh::lean_box(0);
            v___x_3595_ = crate::leanh::lean_apply_1(v_h__1_3591_, v___x_3594_);
            return v___x_3595_;
        } else {
            let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_3591_);
            v___x_3596_ = crate::leanh::lean_apply_4(
                v_h__3_3593_,
                v_x_3589_,
                v_x_3590_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3596_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_3591_);
        if crate::leanh::lean_obj_tag(v_x_3590_) == 0 {
            let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_3592_);
            v___x_3597_ = crate::leanh::lean_apply_4(
                v_h__3_3593_,
                v_x_3589_,
                v_x_3590_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_3597_;
        } else {
            let mut v_head_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_3593_);
            v_head_3598_ = crate::leanh::lean_ctor_get(v_x_3589_, 0);
            crate::leanh::lean_inc(v_head_3598_);
            v_tail_3599_ = crate::leanh::lean_ctor_get(v_x_3589_, 1);
            crate::leanh::lean_inc(v_tail_3599_);
            crate::leanh::lean_dec_ref_known(v_x_3589_, 2);
            v_head_3600_ = crate::leanh::lean_ctor_get(v_x_3590_, 0);
            crate::leanh::lean_inc(v_head_3600_);
            v_tail_3601_ = crate::leanh::lean_ctor_get(v_x_3590_, 1);
            crate::leanh::lean_inc(v_tail_3601_);
            crate::leanh::lean_dec_ref_known(v_x_3590_, 2);
            v___x_3602_ = crate::leanh::lean_apply_4(
                v_h__2_3592_,
                v_head_3598_,
                v_tail_3599_,
                v_head_3600_,
                v_tail_3601_,
            );
            return v___x_3602_;
        }
    }
}
pub unsafe fn l_List_isEqv___redArg(
    mut v_x_3603_: *mut crate::leanh::LeanObject,
    mut v_x_3604_: *mut crate::leanh::LeanObject,
    mut v_x_3605_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: u8 = 0;
    let mut v_head_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: u8 = 0;
    let mut v___x_3615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3603_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_3605_);
                    if crate::leanh::lean_obj_tag(v_x_3604_) == 0 {
                        v___x_3606_ = 1;
                        return v___x_3606_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3604_, 2);
                        v___x_3607_ = 0;
                        return v___x_3607_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3604_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_3603_, 2);
                        crate::leanh::lean_dec_ref(v_x_3605_);
                        v___x_3608_ = 0;
                        return v___x_3608_;
                    } else {
                        v_head_3609_ = crate::leanh::lean_ctor_get(v_x_3603_, 0);
                        crate::leanh::lean_inc(v_head_3609_);
                        v_tail_3610_ = crate::leanh::lean_ctor_get(v_x_3603_, 1);
                        crate::leanh::lean_inc(v_tail_3610_);
                        crate::leanh::lean_dec_ref_known(v_x_3603_, 2);
                        v_head_3611_ = crate::leanh::lean_ctor_get(v_x_3604_, 0);
                        crate::leanh::lean_inc(v_head_3611_);
                        v_tail_3612_ = crate::leanh::lean_ctor_get(v_x_3604_, 1);
                        crate::leanh::lean_inc(v_tail_3612_);
                        crate::leanh::lean_dec_ref_known(v_x_3604_, 2);
                        crate::leanh::lean_inc_ref(v_x_3605_);
                        v___x_3613_ =
                            crate::leanh::lean_apply_2(v_x_3605_, v_head_3609_, v_head_3611_);
                        v___x_3614_ = (crate::leanh::lean_unbox(v___x_3613_) as u8);
                        if v___x_3614_ == 0 {
                            crate::leanh::lean_dec(v_tail_3612_);
                            crate::leanh::lean_dec(v_tail_3610_);
                            crate::leanh::lean_dec_ref(v_x_3605_);
                            v___x_3615_ = (crate::leanh::lean_unbox(v___x_3613_) as u8);
                            return v___x_3615_;
                        } else {
                            v_x_3603_ = v_tail_3610_;
                            v_x_3604_ = v_tail_3612_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isEqv___redArg___boxed(
    mut v_x_3617_: *mut crate::leanh::LeanObject,
    mut v_x_3618_: *mut crate::leanh::LeanObject,
    mut v_x_3619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3620_: u8 = 0;
    let mut v_r_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3620_ = l_List_isEqv___redArg(v_x_3617_, v_x_3618_, v_x_3619_);
    v_r_3621_ = crate::leanh::lean_box((v_res_3620_) as usize);
    return v_r_3621_;
}
pub unsafe fn l_List_isEqv(
    mut v_00_u03b1_3622_: *mut crate::leanh::LeanObject,
    mut v_x_3623_: *mut crate::leanh::LeanObject,
    mut v_x_3624_: *mut crate::leanh::LeanObject,
    mut v_x_3625_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3626_: u8 = 0;
    v___x_3626_ = l_List_isEqv___redArg(v_x_3623_, v_x_3624_, v_x_3625_);
    return v___x_3626_;
}
pub unsafe fn l_List_isEqv___boxed(
    mut v_00_u03b1_3627_: *mut crate::leanh::LeanObject,
    mut v_x_3628_: *mut crate::leanh::LeanObject,
    mut v_x_3629_: *mut crate::leanh::LeanObject,
    mut v_x_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3631_: u8 = 0;
    let mut v_r_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_List_isEqv(v_00_u03b1_3627_, v_x_3628_, v_x_3629_, v_x_3630_);
    v_r_3632_ = crate::leanh::lean_box((v_res_3631_) as usize);
    return v_r_3632_;
}
pub unsafe fn l_List_decidableLex___redArg(
    mut v_inst_3633_: *mut crate::leanh::LeanObject,
    mut v_h_3634_: *mut crate::leanh::LeanObject,
    mut v_x_3635_: *mut crate::leanh::LeanObject,
    mut v_x_3636_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3635_) == 0 {
        crate::leanh::lean_dec_ref(v_h_3634_);
        crate::leanh::lean_dec_ref(v_inst_3633_);
        if crate::leanh::lean_obj_tag(v_x_3636_) == 0 {
            let mut v___x_3637_: u8 = 0;
            v___x_3637_ = 0;
            return v___x_3637_;
        } else {
            let mut v___x_3638_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_3636_, 2);
            v___x_3638_ = 1;
            return v___x_3638_;
        }
    } else {
        let mut v_head_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: u8 = 0;
        v_head_3639_ = crate::leanh::lean_ctor_get(v_x_3635_, 0);
        crate::leanh::lean_inc(v_head_3639_);
        v_tail_3640_ = crate::leanh::lean_ctor_get(v_x_3635_, 1);
        crate::leanh::lean_inc(v_tail_3640_);
        crate::leanh::lean_dec_ref_known(v_x_3635_, 2);
        v___x_3641_ = 0;
        if crate::leanh::lean_obj_tag(v_x_3636_) == 0 {
            crate::leanh::lean_dec(v_tail_3640_);
            crate::leanh::lean_dec(v_head_3639_);
            crate::leanh::lean_dec_ref(v_h_3634_);
            crate::leanh::lean_dec_ref(v_inst_3633_);
            return v___x_3641_;
        } else {
            let mut v_head_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3646_: u8 = 0;
            v_head_3642_ = crate::leanh::lean_ctor_get(v_x_3636_, 0);
            crate::leanh::lean_inc_n(v_head_3642_, 2);
            v_tail_3643_ = crate::leanh::lean_ctor_get(v_x_3636_, 1);
            crate::leanh::lean_inc(v_tail_3643_);
            crate::leanh::lean_dec_ref_known(v_x_3636_, 2);
            crate::leanh::lean_inc_ref(v_inst_3633_);
            crate::leanh::lean_inc(v_head_3639_);
            v___x_3644_ = crate::leanh::lean_apply_2(v_inst_3633_, v_head_3639_, v_head_3642_);
            crate::leanh::lean_inc_ref(v_h_3634_);
            v___x_3645_ = crate::leanh::lean_apply_2(v_h_3634_, v_head_3639_, v_head_3642_);
            v___x_3646_ = (crate::leanh::lean_unbox(v___x_3645_) as u8);
            if v___x_3646_ == 0 {
                let mut v___x_3647_: u8 = 0;
                v___x_3647_ = (crate::leanh::lean_unbox(v___x_3644_) as u8);
                if v___x_3647_ == 0 {
                    crate::leanh::lean_dec(v_tail_3643_);
                    crate::leanh::lean_dec(v_tail_3640_);
                    crate::leanh::lean_dec_ref(v_h_3634_);
                    crate::leanh::lean_dec_ref(v_inst_3633_);
                    return v___x_3641_;
                } else {
                    let mut v___x_3648_: u8 = 0;
                    v___x_3648_ = l_List_decidableLex___redArg(
                        v_inst_3633_,
                        v_h_3634_,
                        v_tail_3640_,
                        v_tail_3643_,
                    );
                    if v___x_3648_ == 0 {
                        return v___x_3641_;
                    } else {
                        return v___x_3648_;
                    }
                }
            } else {
                let mut v___x_3649_: u8 = 0;
                crate::leanh::lean_dec(v_tail_3643_);
                crate::leanh::lean_dec(v_tail_3640_);
                crate::leanh::lean_dec_ref(v_h_3634_);
                crate::leanh::lean_dec_ref(v_inst_3633_);
                v___x_3649_ = (crate::leanh::lean_unbox(v___x_3645_) as u8);
                return v___x_3649_;
            }
        }
    }
}
pub unsafe fn l_List_decidableLex___redArg___boxed(
    mut v_inst_3650_: *mut crate::leanh::LeanObject,
    mut v_h_3651_: *mut crate::leanh::LeanObject,
    mut v_x_3652_: *mut crate::leanh::LeanObject,
    mut v_x_3653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3654_: u8 = 0;
    let mut v_r_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3654_ = l_List_decidableLex___redArg(v_inst_3650_, v_h_3651_, v_x_3652_, v_x_3653_);
    v_r_3655_ = crate::leanh::lean_box((v_res_3654_) as usize);
    return v_r_3655_;
}
pub unsafe fn l_List_decidableLex(
    mut v_00_u03b1_3656_: *mut crate::leanh::LeanObject,
    mut v_inst_3657_: *mut crate::leanh::LeanObject,
    mut v_r_3658_: *mut crate::leanh::LeanObject,
    mut v_h_3659_: *mut crate::leanh::LeanObject,
    mut v_x_3660_: *mut crate::leanh::LeanObject,
    mut v_x_3661_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3662_: u8 = 0;
    v___x_3662_ = l_List_decidableLex___redArg(v_inst_3657_, v_h_3659_, v_x_3660_, v_x_3661_);
    return v___x_3662_;
}
pub unsafe fn l_List_decidableLex___boxed(
    mut v_00_u03b1_3663_: *mut crate::leanh::LeanObject,
    mut v_inst_3664_: *mut crate::leanh::LeanObject,
    mut v_r_3665_: *mut crate::leanh::LeanObject,
    mut v_h_3666_: *mut crate::leanh::LeanObject,
    mut v_x_3667_: *mut crate::leanh::LeanObject,
    mut v_x_3668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3669_: u8 = 0;
    let mut v_r_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_List_decidableLex(
        v_00_u03b1_3663_,
        v_inst_3664_,
        v_r_3665_,
        v_h_3666_,
        v_x_3667_,
        v_x_3668_,
    );
    v_r_3670_ = crate::leanh::lean_box((v_res_3669_) as usize);
    return v_r_3670_;
}
pub unsafe fn l_List_instLT(
    mut v_00_u03b1_3671_: *mut crate::leanh::LeanObject,
    mut v_inst_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = crate::leanh::lean_box(0);
    return v___x_3673_;
}
pub unsafe fn l_List_decidableLT___redArg(
    mut v_inst_3674_: *mut crate::leanh::LeanObject,
    mut v_inst_3675_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3676_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3677_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3678_: u8 = 0;
    v___x_3678_ =
        l_List_decidableLex___redArg(v_inst_3674_, v_inst_3675_, v_l_u2081_3676_, v_l_u2082_3677_);
    return v___x_3678_;
}
pub unsafe fn l_List_decidableLT___redArg___boxed(
    mut v_inst_3679_: *mut crate::leanh::LeanObject,
    mut v_inst_3680_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3681_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3683_: u8 = 0;
    let mut v_r_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3683_ =
        l_List_decidableLT___redArg(v_inst_3679_, v_inst_3680_, v_l_u2081_3681_, v_l_u2082_3682_);
    v_r_3684_ = crate::leanh::lean_box((v_res_3683_) as usize);
    return v_r_3684_;
}
pub unsafe fn l_List_decidableLT(
    mut v_00_u03b1_3685_: *mut crate::leanh::LeanObject,
    mut v_inst_3686_: *mut crate::leanh::LeanObject,
    mut v_inst_3687_: *mut crate::leanh::LeanObject,
    mut v_inst_3688_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3689_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3690_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3691_: u8 = 0;
    v___x_3691_ =
        l_List_decidableLex___redArg(v_inst_3686_, v_inst_3688_, v_l_u2081_3689_, v_l_u2082_3690_);
    return v___x_3691_;
}
pub unsafe fn l_List_decidableLT___boxed(
    mut v_00_u03b1_3692_: *mut crate::leanh::LeanObject,
    mut v_inst_3693_: *mut crate::leanh::LeanObject,
    mut v_inst_3694_: *mut crate::leanh::LeanObject,
    mut v_inst_3695_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3696_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3698_: u8 = 0;
    let mut v_r_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_List_decidableLT(
        v_00_u03b1_3692_,
        v_inst_3693_,
        v_inst_3694_,
        v_inst_3695_,
        v_l_u2081_3696_,
        v_l_u2082_3697_,
    );
    v_r_3699_ = crate::leanh::lean_box((v_res_3698_) as usize);
    return v_r_3699_;
}
pub unsafe fn l_List_instLE(
    mut v_00_u03b1_3700_: *mut crate::leanh::LeanObject,
    mut v_inst_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = crate::leanh::lean_box(0);
    return v___x_3702_;
}
pub unsafe fn l_List_decidableLE___redArg(
    mut v_inst_3703_: *mut crate::leanh::LeanObject,
    mut v_inst_3704_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3705_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3706_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3707_: u8 = 0;
    v___x_3707_ =
        l_List_decidableLex___redArg(v_inst_3703_, v_inst_3704_, v_l_u2082_3706_, v_l_u2081_3705_);
    if v___x_3707_ == 0 {
        let mut v___x_3708_: u8 = 0;
        v___x_3708_ = 1;
        return v___x_3708_;
    } else {
        let mut v___x_3709_: u8 = 0;
        v___x_3709_ = 0;
        return v___x_3709_;
    }
}
pub unsafe fn l_List_decidableLE___redArg___boxed(
    mut v_inst_3710_: *mut crate::leanh::LeanObject,
    mut v_inst_3711_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3712_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3714_: u8 = 0;
    let mut v_r_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3714_ =
        l_List_decidableLE___redArg(v_inst_3710_, v_inst_3711_, v_l_u2081_3712_, v_l_u2082_3713_);
    v_r_3715_ = crate::leanh::lean_box((v_res_3714_) as usize);
    return v_r_3715_;
}
pub unsafe fn l_List_decidableLE(
    mut v_00_u03b1_3716_: *mut crate::leanh::LeanObject,
    mut v_inst_3717_: *mut crate::leanh::LeanObject,
    mut v_inst_3718_: *mut crate::leanh::LeanObject,
    mut v_inst_3719_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3720_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3721_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3722_: u8 = 0;
    v___x_3722_ =
        l_List_decidableLE___redArg(v_inst_3717_, v_inst_3719_, v_l_u2081_3720_, v_l_u2082_3721_);
    return v___x_3722_;
}
pub unsafe fn l_List_decidableLE___boxed(
    mut v_00_u03b1_3723_: *mut crate::leanh::LeanObject,
    mut v_inst_3724_: *mut crate::leanh::LeanObject,
    mut v_inst_3725_: *mut crate::leanh::LeanObject,
    mut v_inst_3726_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3727_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3729_: u8 = 0;
    let mut v_r_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_List_decidableLE(
        v_00_u03b1_3723_,
        v_inst_3724_,
        v_inst_3725_,
        v_inst_3726_,
        v_l_u2081_3727_,
        v_l_u2082_3728_,
    );
    v_r_3730_ = crate::leanh::lean_box((v_res_3729_) as usize);
    return v_r_3730_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_List_lex___auto__1___closed__10;
    v___x_3758_ = l_Lean_mkAtom(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__12_once),
        _init_l_List_lex___auto__1___closed__12,
    );
    v___x_3760_ = l_List_lex___auto__1___closed__5;
    v___x_3761_ = lean_array_push(v___x_3760_, v___x_3759_);
    return v___x_3761_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_List_lex___auto__1___closed__19;
    v___x_3777_ = l_Lean_mkAtom(v___x_3776_);
    return v___x_3777_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3778_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__20_once),
        _init_l_List_lex___auto__1___closed__20,
    );
    v___x_3779_ = l_List_lex___auto__1___closed__5;
    v___x_3780_ = lean_array_push(v___x_3779_, v___x_3778_);
    return v___x_3780_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_List_lex___auto__1___closed__24;
    v___x_3786_ = lean_string_utf8_byte_size(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__25_once),
        _init_l_List_lex___auto__1___closed__25,
    );
    v___x_3788_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3789_ = l_List_lex___auto__1___closed__24;
    v___x_3790_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3788_);
    crate::leanh::lean_ctor_set(v___x_3790_, 2, v___x_3787_);
    return v___x_3790_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = crate::leanh::lean_box(0);
    v___x_3792_ = crate::leanh::lean_box(0);
    v___x_3793_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__26_once),
        _init_l_List_lex___auto__1___closed__26,
    );
    v___x_3794_ = crate::leanh::lean_box(2);
    v___x_3795_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3795_, 0, v___x_3794_);
    crate::leanh::lean_ctor_set(v___x_3795_, 1, v___x_3793_);
    crate::leanh::lean_ctor_set(v___x_3795_, 2, v___x_3792_);
    crate::leanh::lean_ctor_set(v___x_3795_, 3, v___x_3791_);
    return v___x_3795_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__27_once),
        _init_l_List_lex___auto__1___closed__27,
    );
    v___x_3797_ = l_List_lex___auto__1___closed__5;
    v___x_3798_ = lean_array_push(v___x_3797_, v___x_3796_);
    return v___x_3798_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__28_once),
        _init_l_List_lex___auto__1___closed__28,
    );
    v___x_3800_ = l_List_lex___auto__1___closed__23;
    v___x_3801_ = crate::leanh::lean_box(2);
    v___x_3802_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
    crate::leanh::lean_ctor_set(v___x_3802_, 1, v___x_3800_);
    crate::leanh::lean_ctor_set(v___x_3802_, 2, v___x_3799_);
    return v___x_3802_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29_once),
        _init_l_List_lex___auto__1___closed__29,
    );
    v___x_3804_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__21_once),
        _init_l_List_lex___auto__1___closed__21,
    );
    v___x_3805_ = lean_array_push(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__30_once),
        _init_l_List_lex___auto__1___closed__30,
    );
    v___x_3807_ = l_List_lex___auto__1___closed__18;
    v___x_3808_ = crate::leanh::lean_box(2);
    v___x_3809_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3808_);
    crate::leanh::lean_ctor_set(v___x_3809_, 1, v___x_3807_);
    crate::leanh::lean_ctor_set(v___x_3809_, 2, v___x_3806_);
    return v___x_3809_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__31_once),
        _init_l_List_lex___auto__1___closed__31,
    );
    v___x_3811_ = l_List_lex___auto__1___closed__5;
    v___x_3812_ = lean_array_push(v___x_3811_, v___x_3810_);
    return v___x_3812_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_List_lex___auto__1___closed__37;
    v___x_3824_ = l_Lean_mkAtom(v___x_3823_);
    return v___x_3824_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__39() -> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__38_once),
        _init_l_List_lex___auto__1___closed__38,
    );
    v___x_3826_ = l_List_lex___auto__1___closed__5;
    v___x_3827_ = lean_array_push(v___x_3826_, v___x_3825_);
    return v___x_3827_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29_once),
        _init_l_List_lex___auto__1___closed__29,
    );
    v___x_3829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__39_once),
        _init_l_List_lex___auto__1___closed__39,
    );
    v___x_3830_ = lean_array_push(v___x_3829_, v___x_3828_);
    return v___x_3830_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__41() -> *mut crate::leanh::LeanObject {
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__40_once),
        _init_l_List_lex___auto__1___closed__40,
    );
    v___x_3832_ = l_List_lex___auto__1___closed__36;
    v___x_3833_ = crate::leanh::lean_box(2);
    v___x_3834_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3834_, 0, v___x_3833_);
    crate::leanh::lean_ctor_set(v___x_3834_, 1, v___x_3832_);
    crate::leanh::lean_ctor_set(v___x_3834_, 2, v___x_3831_);
    return v___x_3834_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__42() -> *mut crate::leanh::LeanObject {
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41_once),
        _init_l_List_lex___auto__1___closed__41,
    );
    v___x_3836_ = l_List_lex___auto__1___closed__5;
    v___x_3837_ = lean_array_push(v___x_3836_, v___x_3835_);
    return v___x_3837_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_List_lex___auto__1___closed__43;
    v___x_3840_ = l_Lean_mkAtom(v___x_3839_);
    return v___x_3840_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__44_once),
        _init_l_List_lex___auto__1___closed__44,
    );
    v___x_3842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__42_once),
        _init_l_List_lex___auto__1___closed__42,
    );
    v___x_3843_ = lean_array_push(v___x_3842_, v___x_3841_);
    return v___x_3843_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41_once),
        _init_l_List_lex___auto__1___closed__41,
    );
    v___x_3845_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__45_once),
        _init_l_List_lex___auto__1___closed__45,
    );
    v___x_3846_ = lean_array_push(v___x_3845_, v___x_3844_);
    return v___x_3846_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__47() -> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__46_once),
        _init_l_List_lex___auto__1___closed__46,
    );
    v___x_3848_ = l_List_lex___auto__1___closed__34;
    v___x_3849_ = crate::leanh::lean_box(2);
    v___x_3850_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3850_, 0, v___x_3849_);
    crate::leanh::lean_ctor_set(v___x_3850_, 1, v___x_3848_);
    crate::leanh::lean_ctor_set(v___x_3850_, 2, v___x_3847_);
    return v___x_3850_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__48() -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__47_once),
        _init_l_List_lex___auto__1___closed__47,
    );
    v___x_3852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__32_once),
        _init_l_List_lex___auto__1___closed__32,
    );
    v___x_3853_ = lean_array_push(v___x_3852_, v___x_3851_);
    return v___x_3853_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__50() -> *mut crate::leanh::LeanObject {
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ = l_List_lex___auto__1___closed__49;
    v___x_3856_ = l_Lean_mkAtom(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__51() -> *mut crate::leanh::LeanObject {
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3857_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__50_once),
        _init_l_List_lex___auto__1___closed__50,
    );
    v___x_3858_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__48_once),
        _init_l_List_lex___auto__1___closed__48,
    );
    v___x_3859_ = lean_array_push(v___x_3858_, v___x_3857_);
    return v___x_3859_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__52() -> *mut crate::leanh::LeanObject {
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__51_once),
        _init_l_List_lex___auto__1___closed__51,
    );
    v___x_3861_ = l_List_lex___auto__1___closed__16;
    v___x_3862_ = crate::leanh::lean_box(2);
    v___x_3863_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3863_, 0, v___x_3862_);
    crate::leanh::lean_ctor_set(v___x_3863_, 1, v___x_3861_);
    crate::leanh::lean_ctor_set(v___x_3863_, 2, v___x_3860_);
    return v___x_3863_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__53() -> *mut crate::leanh::LeanObject {
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__52_once),
        _init_l_List_lex___auto__1___closed__52,
    );
    v___x_3865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__13_once),
        _init_l_List_lex___auto__1___closed__13,
    );
    v___x_3866_ = lean_array_push(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__54() -> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__53_once),
        _init_l_List_lex___auto__1___closed__53,
    );
    v___x_3868_ = l_List_lex___auto__1___closed__11;
    v___x_3869_ = crate::leanh::lean_box(2);
    v___x_3870_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
    crate::leanh::lean_ctor_set(v___x_3870_, 1, v___x_3868_);
    crate::leanh::lean_ctor_set(v___x_3870_, 2, v___x_3867_);
    return v___x_3870_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__55() -> *mut crate::leanh::LeanObject {
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__54_once),
        _init_l_List_lex___auto__1___closed__54,
    );
    v___x_3872_ = l_List_lex___auto__1___closed__5;
    v___x_3873_ = lean_array_push(v___x_3872_, v___x_3871_);
    return v___x_3873_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__56() -> *mut crate::leanh::LeanObject {
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__55_once),
        _init_l_List_lex___auto__1___closed__55,
    );
    v___x_3875_ = l_List_lex___auto__1___closed__9;
    v___x_3876_ = crate::leanh::lean_box(2);
    v___x_3877_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3877_, 0, v___x_3876_);
    crate::leanh::lean_ctor_set(v___x_3877_, 1, v___x_3875_);
    crate::leanh::lean_ctor_set(v___x_3877_, 2, v___x_3874_);
    return v___x_3877_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__57() -> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__56_once),
        _init_l_List_lex___auto__1___closed__56,
    );
    v___x_3879_ = l_List_lex___auto__1___closed__5;
    v___x_3880_ = lean_array_push(v___x_3879_, v___x_3878_);
    return v___x_3880_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__58() -> *mut crate::leanh::LeanObject {
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__57_once),
        _init_l_List_lex___auto__1___closed__57,
    );
    v___x_3882_ = l_List_lex___auto__1___closed__7;
    v___x_3883_ = crate::leanh::lean_box(2);
    v___x_3884_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3883_);
    crate::leanh::lean_ctor_set(v___x_3884_, 1, v___x_3882_);
    crate::leanh::lean_ctor_set(v___x_3884_, 2, v___x_3881_);
    return v___x_3884_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__59() -> *mut crate::leanh::LeanObject {
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__58_once),
        _init_l_List_lex___auto__1___closed__58,
    );
    v___x_3886_ = l_List_lex___auto__1___closed__5;
    v___x_3887_ = lean_array_push(v___x_3886_, v___x_3885_);
    return v___x_3887_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__60() -> *mut crate::leanh::LeanObject {
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3888_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__59_once),
        _init_l_List_lex___auto__1___closed__59,
    );
    v___x_3889_ = l_List_lex___auto__1___closed__4;
    v___x_3890_ = crate::leanh::lean_box(2);
    v___x_3891_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3890_);
    crate::leanh::lean_ctor_set(v___x_3891_, 1, v___x_3889_);
    crate::leanh::lean_ctor_set(v___x_3891_, 2, v___x_3888_);
    return v___x_3891_;
}
pub unsafe fn _init_l_List_lex___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__60_once),
        _init_l_List_lex___auto__1___closed__60,
    );
    return v___x_3892_;
}
pub unsafe fn l_List_lex___redArg(
    mut v_inst_3893_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3894_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3895_: *mut crate::leanh::LeanObject,
    mut v_lt_3896_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: u8 = 0;
    let mut v_head_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_u2081_3894_) == 0 {
                    crate::leanh::lean_dec_ref(v_lt_3896_);
                    crate::leanh::lean_dec_ref(v_inst_3893_);
                    if crate::leanh::lean_obj_tag(v_l_u2082_3895_) == 0 {
                        v___x_3897_ = 0;
                        return v___x_3897_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_u2082_3895_, 2);
                        v___x_3898_ = 1;
                        return v___x_3898_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_u2082_3895_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_l_u2081_3894_, 2);
                        crate::leanh::lean_dec_ref(v_lt_3896_);
                        crate::leanh::lean_dec_ref(v_inst_3893_);
                        v___x_3899_ = 0;
                        return v___x_3899_;
                    } else {
                        v_head_3900_ = crate::leanh::lean_ctor_get(v_l_u2081_3894_, 0);
                        crate::leanh::lean_inc_n(v_head_3900_, 2);
                        v_tail_3901_ = crate::leanh::lean_ctor_get(v_l_u2081_3894_, 1);
                        crate::leanh::lean_inc(v_tail_3901_);
                        crate::leanh::lean_dec_ref_known(v_l_u2081_3894_, 2);
                        v_head_3902_ = crate::leanh::lean_ctor_get(v_l_u2082_3895_, 0);
                        crate::leanh::lean_inc_n(v_head_3902_, 2);
                        v_tail_3903_ = crate::leanh::lean_ctor_get(v_l_u2082_3895_, 1);
                        crate::leanh::lean_inc(v_tail_3903_);
                        crate::leanh::lean_dec_ref_known(v_l_u2082_3895_, 2);
                        crate::leanh::lean_inc_ref(v_lt_3896_);
                        v___x_3904_ =
                            crate::leanh::lean_apply_2(v_lt_3896_, v_head_3900_, v_head_3902_);
                        v___x_3905_ = (crate::leanh::lean_unbox(v___x_3904_) as u8);
                        if v___x_3905_ == 0 {
                            crate::leanh::lean_inc_ref(v_inst_3893_);
                            v___x_3906_ = crate::leanh::lean_apply_2(
                                v_inst_3893_,
                                v_head_3900_,
                                v_head_3902_,
                            );
                            v___x_3907_ = (crate::leanh::lean_unbox(v___x_3906_) as u8);
                            if v___x_3907_ == 0 {
                                crate::leanh::lean_dec(v_tail_3903_);
                                crate::leanh::lean_dec(v_tail_3901_);
                                crate::leanh::lean_dec_ref(v_lt_3896_);
                                crate::leanh::lean_dec_ref(v_inst_3893_);
                                v___x_3908_ = (crate::leanh::lean_unbox(v___x_3906_) as u8);
                                return v___x_3908_;
                            } else {
                                v_l_u2081_3894_ = v_tail_3901_;
                                v_l_u2082_3895_ = v_tail_3903_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_3903_);
                            crate::leanh::lean_dec(v_head_3902_);
                            crate::leanh::lean_dec(v_tail_3901_);
                            crate::leanh::lean_dec(v_head_3900_);
                            crate::leanh::lean_dec_ref(v_lt_3896_);
                            crate::leanh::lean_dec_ref(v_inst_3893_);
                            v___x_3910_ = (crate::leanh::lean_unbox(v___x_3904_) as u8);
                            return v___x_3910_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lex___redArg___boxed(
    mut v_inst_3911_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3912_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3913_: *mut crate::leanh::LeanObject,
    mut v_lt_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3915_: u8 = 0;
    let mut v_r_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3915_ = l_List_lex___redArg(v_inst_3911_, v_l_u2081_3912_, v_l_u2082_3913_, v_lt_3914_);
    v_r_3916_ = crate::leanh::lean_box((v_res_3915_) as usize);
    return v_r_3916_;
}
pub unsafe fn l_List_lex(
    mut v_00_u03b1_3917_: *mut crate::leanh::LeanObject,
    mut v_inst_3918_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3919_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3920_: *mut crate::leanh::LeanObject,
    mut v_lt_3921_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3922_: u8 = 0;
    v___x_3922_ = l_List_lex___redArg(v_inst_3918_, v_l_u2081_3919_, v_l_u2082_3920_, v_lt_3921_);
    return v___x_3922_;
}
pub unsafe fn l_List_lex___boxed(
    mut v_00_u03b1_3923_: *mut crate::leanh::LeanObject,
    mut v_inst_3924_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_3925_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3926_: *mut crate::leanh::LeanObject,
    mut v_lt_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3928_: u8 = 0;
    let mut v_r_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3928_ = l_List_lex(
        v_00_u03b1_3923_,
        v_inst_3924_,
        v_l_u2081_3925_,
        v_l_u2082_3926_,
        v_lt_3927_,
    );
    v_r_3929_ = crate::leanh::lean_box((v_res_3928_) as usize);
    return v_r_3929_;
}
pub unsafe fn l_List_getLast___redArg(
    mut v_x_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tail_3931_ = crate::leanh::lean_ctor_get(v_x_3930_, 1);
                if crate::leanh::lean_obj_tag(v_tail_3931_) == 0 {
                    v_head_3932_ = crate::leanh::lean_ctor_get(v_x_3930_, 0);
                    crate::leanh::lean_inc(v_head_3932_);
                    return v_head_3932_;
                } else {
                    v_x_3930_ = v_tail_3931_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_getLast___redArg___boxed(
    mut v_x_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_List_getLast___redArg(v_x_3934_);
    crate::leanh::lean_dec(v_x_3934_);
    return v_res_3935_;
}
pub unsafe fn l_List_getLast(
    mut v_00_u03b1_3936_: *mut crate::leanh::LeanObject,
    mut v_x_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_List_getLast___redArg(v_x_3937_);
    return v___x_3939_;
}
pub unsafe fn l_List_getLast___boxed(
    mut v_00_u03b1_3940_: *mut crate::leanh::LeanObject,
    mut v_x_3941_: *mut crate::leanh::LeanObject,
    mut v_x_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_List_getLast(v_00_u03b1_3940_, v_x_3941_, v_x_3942_);
    crate::leanh::lean_dec(v_x_3941_);
    return v_res_3943_;
}
pub unsafe fn l_List_getLast_x3f___redArg(
    mut v_x_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3944_) == 0 {
        let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3945_ = crate::leanh::lean_box(0);
        return v___x_3945_;
    } else {
        let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3946_ = l_List_getLast___redArg(v_x_3944_);
        v___x_3947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3947_, 0, v___x_3946_);
        return v___x_3947_;
    }
}
pub unsafe fn l_List_getLast_x3f___redArg___boxed(
    mut v_x_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3949_ = l_List_getLast_x3f___redArg(v_x_3948_);
    crate::leanh::lean_dec(v_x_3948_);
    return v_res_3949_;
}
pub unsafe fn l_List_getLast_x3f(
    mut v_00_u03b1_3950_: *mut crate::leanh::LeanObject,
    mut v_x_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_List_getLast_x3f___redArg(v_x_3951_);
    return v___x_3952_;
}
pub unsafe fn l_List_getLast_x3f___boxed(
    mut v_00_u03b1_3953_: *mut crate::leanh::LeanObject,
    mut v_x_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l_List_getLast_x3f(v_00_u03b1_3953_, v_x_3954_);
    crate::leanh::lean_dec(v_x_3954_);
    return v_res_3955_;
}
pub unsafe fn l_List_getLastD___redArg(
    mut v_x_3956_: *mut crate::leanh::LeanObject,
    mut v_x_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3956_) == 0 {
        crate::leanh::lean_inc(v_x_3957_);
        return v_x_3957_;
    } else {
        let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3958_ = l_List_getLast___redArg(v_x_3956_);
        return v___x_3958_;
    }
}
pub unsafe fn l_List_getLastD___redArg___boxed(
    mut v_x_3959_: *mut crate::leanh::LeanObject,
    mut v_x_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_List_getLastD___redArg(v_x_3959_, v_x_3960_);
    crate::leanh::lean_dec(v_x_3960_);
    crate::leanh::lean_dec(v_x_3959_);
    return v_res_3961_;
}
pub unsafe fn l_List_getLastD(
    mut v_00_u03b1_3962_: *mut crate::leanh::LeanObject,
    mut v_x_3963_: *mut crate::leanh::LeanObject,
    mut v_x_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_List_getLastD___redArg(v_x_3963_, v_x_3964_);
    return v___x_3965_;
}
pub unsafe fn l_List_getLastD___boxed(
    mut v_00_u03b1_3966_: *mut crate::leanh::LeanObject,
    mut v_x_3967_: *mut crate::leanh::LeanObject,
    mut v_x_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_List_getLastD(v_00_u03b1_3966_, v_x_3967_, v_x_3968_);
    crate::leanh::lean_dec(v_x_3968_);
    crate::leanh::lean_dec(v_x_3967_);
    return v_res_3969_;
}
pub unsafe fn l_List_head___redArg(
    mut v_x_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_3971_ = crate::leanh::lean_ctor_get(v_x_3970_, 0);
    crate::leanh::lean_inc(v_head_3971_);
    return v_head_3971_;
}
pub unsafe fn l_List_head___redArg___boxed(
    mut v_x_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_List_head___redArg(v_x_3972_);
    crate::leanh::lean_dec(v_x_3972_);
    return v_res_3973_;
}
pub unsafe fn l_List_head(
    mut v_00_u03b1_3974_: *mut crate::leanh::LeanObject,
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_3977_ = crate::leanh::lean_ctor_get(v_x_3975_, 0);
    crate::leanh::lean_inc(v_head_3977_);
    return v_head_3977_;
}
pub unsafe fn l_List_head___boxed(
    mut v_00_u03b1_3978_: *mut crate::leanh::LeanObject,
    mut v_x_3979_: *mut crate::leanh::LeanObject,
    mut v_x_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3981_ = l_List_head(v_00_u03b1_3978_, v_x_3979_, v_x_3980_);
    crate::leanh::lean_dec(v_x_3979_);
    return v_res_3981_;
}
pub unsafe fn l_List_head_x3f___redArg(
    mut v_x_3982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3982_) == 0 {
        let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3983_ = crate::leanh::lean_box(0);
        return v___x_3983_;
    } else {
        let mut v_head_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_3984_ = crate::leanh::lean_ctor_get(v_x_3982_, 0);
        crate::leanh::lean_inc(v_head_3984_);
        v___x_3985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3985_, 0, v_head_3984_);
        return v___x_3985_;
    }
}
pub unsafe fn l_List_head_x3f___redArg___boxed(
    mut v_x_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_List_head_x3f___redArg(v_x_3986_);
    crate::leanh::lean_dec(v_x_3986_);
    return v_res_3987_;
}
pub unsafe fn l_List_head_x3f(
    mut v_00_u03b1_3988_: *mut crate::leanh::LeanObject,
    mut v_x_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = l_List_head_x3f___redArg(v_x_3989_);
    return v___x_3990_;
}
pub unsafe fn l_List_head_x3f___boxed(
    mut v_00_u03b1_3991_: *mut crate::leanh::LeanObject,
    mut v_x_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3993_ = l_List_head_x3f(v_00_u03b1_3991_, v_x_3992_);
    crate::leanh::lean_dec(v_x_3992_);
    return v_res_3993_;
}
pub unsafe fn l_List_headD___redArg(
    mut v_x_3994_: *mut crate::leanh::LeanObject,
    mut v_x_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3994_) == 0 {
        crate::leanh::lean_inc(v_x_3995_);
        return v_x_3995_;
    } else {
        let mut v_head_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_3996_ = crate::leanh::lean_ctor_get(v_x_3994_, 0);
        crate::leanh::lean_inc(v_head_3996_);
        return v_head_3996_;
    }
}
pub unsafe fn l_List_headD___redArg___boxed(
    mut v_x_3997_: *mut crate::leanh::LeanObject,
    mut v_x_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_List_headD___redArg(v_x_3997_, v_x_3998_);
    crate::leanh::lean_dec(v_x_3998_);
    crate::leanh::lean_dec(v_x_3997_);
    return v_res_3999_;
}
pub unsafe fn l_List_headD(
    mut v_00_u03b1_4000_: *mut crate::leanh::LeanObject,
    mut v_x_4001_: *mut crate::leanh::LeanObject,
    mut v_x_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4001_) == 0 {
        crate::leanh::lean_inc(v_x_4002_);
        return v_x_4002_;
    } else {
        let mut v_head_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_4003_ = crate::leanh::lean_ctor_get(v_x_4001_, 0);
        crate::leanh::lean_inc(v_head_4003_);
        return v_head_4003_;
    }
}
pub unsafe fn l_List_headD___boxed(
    mut v_00_u03b1_4004_: *mut crate::leanh::LeanObject,
    mut v_x_4005_: *mut crate::leanh::LeanObject,
    mut v_x_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4007_ = l_List_headD(v_00_u03b1_4004_, v_x_4005_, v_x_4006_);
    crate::leanh::lean_dec(v_x_4006_);
    crate::leanh::lean_dec(v_x_4005_);
    return v_res_4007_;
}
pub unsafe fn l_List_tail___redArg(
    mut v_x_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4008_) == 0 {
        return v_x_4008_;
    } else {
        let mut v_tail_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4009_ = crate::leanh::lean_ctor_get(v_x_4008_, 1);
        crate::leanh::lean_inc(v_tail_4009_);
        return v_tail_4009_;
    }
}
pub unsafe fn l_List_tail___redArg___boxed(
    mut v_x_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_List_tail___redArg(v_x_4010_);
    crate::leanh::lean_dec(v_x_4010_);
    return v_res_4011_;
}
pub unsafe fn l_List_tail(
    mut v_00_u03b1_4012_: *mut crate::leanh::LeanObject,
    mut v_x_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4013_) == 0 {
        return v_x_4013_;
    } else {
        let mut v_tail_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4014_ = crate::leanh::lean_ctor_get(v_x_4013_, 1);
        crate::leanh::lean_inc(v_tail_4014_);
        return v_tail_4014_;
    }
}
pub unsafe fn l_List_tail___boxed(
    mut v_00_u03b1_4015_: *mut crate::leanh::LeanObject,
    mut v_x_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_List_tail(v_00_u03b1_4015_, v_x_4016_);
    crate::leanh::lean_dec(v_x_4016_);
    return v_res_4017_;
}
pub unsafe fn l_List_tail_x3f___redArg(
    mut v_x_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4018_) == 0 {
        let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4019_ = crate::leanh::lean_box(0);
        return v___x_4019_;
    } else {
        let mut v_tail_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4020_ = crate::leanh::lean_ctor_get(v_x_4018_, 1);
        crate::leanh::lean_inc(v_tail_4020_);
        v___x_4021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4021_, 0, v_tail_4020_);
        return v___x_4021_;
    }
}
pub unsafe fn l_List_tail_x3f___redArg___boxed(
    mut v_x_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_List_tail_x3f___redArg(v_x_4022_);
    crate::leanh::lean_dec(v_x_4022_);
    return v_res_4023_;
}
pub unsafe fn l_List_tail_x3f(
    mut v_00_u03b1_4024_: *mut crate::leanh::LeanObject,
    mut v_x_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_List_tail_x3f___redArg(v_x_4025_);
    return v___x_4026_;
}
pub unsafe fn l_List_tail_x3f___boxed(
    mut v_00_u03b1_4027_: *mut crate::leanh::LeanObject,
    mut v_x_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_List_tail_x3f(v_00_u03b1_4027_, v_x_4028_);
    crate::leanh::lean_dec(v_x_4028_);
    return v_res_4029_;
}
pub unsafe fn l_List_tailD___redArg(
    mut v_l_4030_: *mut crate::leanh::LeanObject,
    mut v_fallback_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4030_) == 0 {
        crate::leanh::lean_inc(v_fallback_4031_);
        return v_fallback_4031_;
    } else {
        let mut v_tail_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4032_ = crate::leanh::lean_ctor_get(v_l_4030_, 1);
        crate::leanh::lean_inc(v_tail_4032_);
        return v_tail_4032_;
    }
}
pub unsafe fn l_List_tailD___redArg___boxed(
    mut v_l_4033_: *mut crate::leanh::LeanObject,
    mut v_fallback_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_List_tailD___redArg(v_l_4033_, v_fallback_4034_);
    crate::leanh::lean_dec(v_fallback_4034_);
    crate::leanh::lean_dec(v_l_4033_);
    return v_res_4035_;
}
pub unsafe fn l_List_tailD(
    mut v_00_u03b1_4036_: *mut crate::leanh::LeanObject,
    mut v_l_4037_: *mut crate::leanh::LeanObject,
    mut v_fallback_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_l_4037_) == 0 {
        crate::leanh::lean_inc(v_fallback_4038_);
        return v_fallback_4038_;
    } else {
        let mut v_tail_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4039_ = crate::leanh::lean_ctor_get(v_l_4037_, 1);
        crate::leanh::lean_inc(v_tail_4039_);
        return v_tail_4039_;
    }
}
pub unsafe fn l_List_tailD___boxed(
    mut v_00_u03b1_4040_: *mut crate::leanh::LeanObject,
    mut v_l_4041_: *mut crate::leanh::LeanObject,
    mut v_fallback_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ = l_List_tailD(v_00_u03b1_4040_, v_l_4041_, v_fallback_4042_);
    crate::leanh::lean_dec(v_fallback_4042_);
    crate::leanh::lean_dec(v_l_4041_);
    return v_res_4043_;
}
pub unsafe fn l_List_filter___redArg(
    mut v_p_4044_: *mut crate::leanh::LeanObject,
    mut v_x_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4045_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_4044_);
                    return v_x_4045_;
                } else {
                    v_head_4046_ = crate::leanh::lean_ctor_get(v_x_4045_, 0);
                    v_tail_4047_ = crate::leanh::lean_ctor_get(v_x_4045_, 1);
                    v_isSharedCheck_4058_ = (!crate::leanh::lean_is_exclusive(v_x_4045_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4049_ = v_x_4045_;
                        v_isShared_4050_ = v_isSharedCheck_4058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4047_);
                        crate::leanh::lean_inc(v_head_4046_);
                        crate::leanh::lean_dec(v_x_4045_);
                        v___x_4049_ = crate::leanh::lean_box(0);
                        v_isShared_4050_ = v_isSharedCheck_4058_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_p_4044_);
                crate::leanh::lean_inc(v_head_4046_);
                v___x_4051_ = crate::leanh::lean_apply_1(v_p_4044_, v_head_4046_);
                v___x_4052_ = (crate::leanh::lean_unbox(v___x_4051_) as u8);
                if v___x_4052_ == 0 {
                    crate::leanh::lean_del_object(v___x_4049_);
                    crate::leanh::lean_dec(v_head_4046_);
                    v_x_4045_ = v_tail_4047_;
                    state = 0;
                    continue;
                } else {
                    v___x_4054_ = l_List_filter___redArg(v_p_4044_, v_tail_4047_);
                    if v_isShared_4050_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4049_, 1, v___x_4054_);
                        v___x_4056_ = v___x_4049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_head_4046_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4054_);
                        v___x_4056_ = v_reuseFailAlloc_4057_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filter(
    mut v_00_u03b1_4059_: *mut crate::leanh::LeanObject,
    mut v_p_4060_: *mut crate::leanh::LeanObject,
    mut v_x_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_List_filter___redArg(v_p_4060_, v_x_4061_);
    return v___x_4062_;
}
pub unsafe fn l_List_foldr___redArg(
    mut v_f_4063_: *mut crate::leanh::LeanObject,
    mut v_init_4064_: *mut crate::leanh::LeanObject,
    mut v_x_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4065_) == 0 {
        crate::leanh::lean_dec(v_f_4063_);
        crate::leanh::lean_inc(v_init_4064_);
        return v_init_4064_;
    } else {
        let mut v_head_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_4066_ = crate::leanh::lean_ctor_get(v_x_4065_, 0);
        crate::leanh::lean_inc(v_head_4066_);
        v_tail_4067_ = crate::leanh::lean_ctor_get(v_x_4065_, 1);
        crate::leanh::lean_inc(v_tail_4067_);
        crate::leanh::lean_dec_ref_known(v_x_4065_, 2);
        crate::leanh::lean_inc(v_f_4063_);
        v___x_4068_ = l_List_foldr___redArg(v_f_4063_, v_init_4064_, v_tail_4067_);
        v___x_4069_ = crate::leanh::lean_apply_2(v_f_4063_, v_head_4066_, v___x_4068_);
        return v___x_4069_;
    }
}
pub unsafe fn l_List_foldr___redArg___boxed(
    mut v_f_4070_: *mut crate::leanh::LeanObject,
    mut v_init_4071_: *mut crate::leanh::LeanObject,
    mut v_x_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_List_foldr___redArg(v_f_4070_, v_init_4071_, v_x_4072_);
    crate::leanh::lean_dec(v_init_4071_);
    return v_res_4073_;
}
pub unsafe fn l_List_foldr(
    mut v_00_u03b1_4074_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4075_: *mut crate::leanh::LeanObject,
    mut v_f_4076_: *mut crate::leanh::LeanObject,
    mut v_init_4077_: *mut crate::leanh::LeanObject,
    mut v_x_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4079_ = l_List_foldr___redArg(v_f_4076_, v_init_4077_, v_x_4078_);
    return v___x_4079_;
}
pub unsafe fn l_List_foldr___boxed(
    mut v_00_u03b1_4080_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4081_: *mut crate::leanh::LeanObject,
    mut v_f_4082_: *mut crate::leanh::LeanObject,
    mut v_init_4083_: *mut crate::leanh::LeanObject,
    mut v_x_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_List_foldr(
        v_00_u03b1_4080_,
        v_00_u03b2_4081_,
        v_f_4082_,
        v_init_4083_,
        v_x_4084_,
    );
    crate::leanh::lean_dec(v_init_4083_);
    return v_res_4085_;
}
pub unsafe fn l_List_reverseAux___redArg(
    mut v_x_4086_: *mut crate::leanh::LeanObject,
    mut v_x_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4086_) == 0 {
                    return v_x_4087_;
                } else {
                    v_head_4088_ = crate::leanh::lean_ctor_get(v_x_4086_, 0);
                    v_tail_4089_ = crate::leanh::lean_ctor_get(v_x_4086_, 1);
                    v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v_x_4086_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4091_ = v_x_4086_;
                        v_isShared_4092_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4089_);
                        crate::leanh::lean_inc(v_head_4088_);
                        crate::leanh::lean_dec(v_x_4086_);
                        v___x_4091_ = crate::leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4091_, 1, v_x_4087_);
                    v___x_4094_ = v___x_4091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_head_4088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 1, v_x_4087_);
                    v___x_4094_ = v_reuseFailAlloc_4096_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_4086_ = v_tail_4089_;
                v_x_4087_ = v___x_4094_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_reverseAux(
    mut v_00_u03b1_4098_: *mut crate::leanh::LeanObject,
    mut v_x_4099_: *mut crate::leanh::LeanObject,
    mut v_x_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = l_List_reverseAux___redArg(v_x_4099_, v_x_4100_);
    return v___x_4101_;
}
pub unsafe fn l_List_reverse___redArg(
    mut v_as_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4103_ = crate::leanh::lean_box(0);
    v___x_4104_ = l_List_reverseAux___redArg(v_as_4102_, v___x_4103_);
    return v___x_4104_;
}
pub unsafe fn l_List_reverse(
    mut v_00_u03b1_4105_: *mut crate::leanh::LeanObject,
    mut v_as_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_List_reverse___redArg(v_as_4106_);
    return v___x_4107_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: *mut crate::leanh::LeanObject,
    mut v_h__1_4110_: *mut crate::leanh::LeanObject,
    mut v_h__2_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4108_) == 0 {
        let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4111_);
        v___x_4112_ = crate::leanh::lean_apply_1(v_h__1_4110_, v_x_4109_);
        return v___x_4112_;
    } else {
        let mut v_head_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4110_);
        v_head_4113_ = crate::leanh::lean_ctor_get(v_x_4108_, 0);
        crate::leanh::lean_inc(v_head_4113_);
        v_tail_4114_ = crate::leanh::lean_ctor_get(v_x_4108_, 1);
        crate::leanh::lean_inc(v_tail_4114_);
        crate::leanh::lean_dec_ref_known(v_x_4108_, 2);
        v___x_4115_ =
            crate::leanh::lean_apply_3(v_h__2_4111_, v_head_4113_, v_tail_4114_, v_x_4109_);
        return v___x_4115_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_4116_: *mut crate::leanh::LeanObject,
    mut v_motive_4117_: *mut crate::leanh::LeanObject,
    mut v_x_4118_: *mut crate::leanh::LeanObject,
    mut v_x_4119_: *mut crate::leanh::LeanObject,
    mut v_h__1_4120_: *mut crate::leanh::LeanObject,
    mut v_h__2_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4118_) == 0 {
        let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4121_);
        v___x_4122_ = crate::leanh::lean_apply_1(v_h__1_4120_, v_x_4119_);
        return v___x_4122_;
    } else {
        let mut v_head_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4120_);
        v_head_4123_ = crate::leanh::lean_ctor_get(v_x_4118_, 0);
        crate::leanh::lean_inc(v_head_4123_);
        v_tail_4124_ = crate::leanh::lean_ctor_get(v_x_4118_, 1);
        crate::leanh::lean_inc(v_tail_4124_);
        crate::leanh::lean_dec_ref_known(v_x_4118_, 2);
        v___x_4125_ =
            crate::leanh::lean_apply_3(v_h__2_4121_, v_head_4123_, v_tail_4124_, v_x_4119_);
        return v___x_4125_;
    }
}
pub unsafe fn l_List_appendTR___redArg(
    mut v_as_4126_: *mut crate::leanh::LeanObject,
    mut v_bs_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l_List_reverse___redArg(v_as_4126_);
    v___x_4129_ = l_List_reverseAux___redArg(v___x_4128_, v_bs_4127_);
    return v___x_4129_;
}
pub unsafe fn l_List_appendTR(
    mut v_00_u03b1_4130_: *mut crate::leanh::LeanObject,
    mut v_as_4131_: *mut crate::leanh::LeanObject,
    mut v_bs_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = l_List_appendTR___redArg(v_as_4131_, v_bs_4132_);
    return v___x_4133_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(
    mut v_x_4134_: *mut crate::leanh::LeanObject,
    mut v_x_4135_: *mut crate::leanh::LeanObject,
    mut v_h__1_4136_: *mut crate::leanh::LeanObject,
    mut v_h__2_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4134_) == 0 {
        let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4137_);
        v___x_4138_ = crate::leanh::lean_apply_1(v_h__1_4136_, v_x_4135_);
        return v___x_4138_;
    } else {
        let mut v_head_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4136_);
        v_head_4139_ = crate::leanh::lean_ctor_get(v_x_4134_, 0);
        crate::leanh::lean_inc(v_head_4139_);
        v_tail_4140_ = crate::leanh::lean_ctor_get(v_x_4134_, 1);
        crate::leanh::lean_inc(v_tail_4140_);
        crate::leanh::lean_dec_ref_known(v_x_4134_, 2);
        v___x_4141_ =
            crate::leanh::lean_apply_3(v_h__2_4137_, v_head_4139_, v_tail_4140_, v_x_4135_);
        return v___x_4141_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(
    mut v_00_u03b1_4142_: *mut crate::leanh::LeanObject,
    mut v_motive_4143_: *mut crate::leanh::LeanObject,
    mut v_x_4144_: *mut crate::leanh::LeanObject,
    mut v_x_4145_: *mut crate::leanh::LeanObject,
    mut v_h__1_4146_: *mut crate::leanh::LeanObject,
    mut v_h__2_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4144_) == 0 {
        let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4147_);
        v___x_4148_ = crate::leanh::lean_apply_1(v_h__1_4146_, v_x_4145_);
        return v___x_4148_;
    } else {
        let mut v_head_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4146_);
        v_head_4149_ = crate::leanh::lean_ctor_get(v_x_4144_, 0);
        crate::leanh::lean_inc(v_head_4149_);
        v_tail_4150_ = crate::leanh::lean_ctor_get(v_x_4144_, 1);
        crate::leanh::lean_inc(v_tail_4150_);
        crate::leanh::lean_dec_ref_known(v_x_4144_, 2);
        v___x_4151_ =
            crate::leanh::lean_apply_3(v_h__2_4147_, v_head_4149_, v_tail_4150_, v_x_4145_);
        return v___x_4151_;
    }
}
pub unsafe fn l_List_instAppend(
    mut v_00_u03b1_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_List_instAppend___closed__0;
    return v___x_4154_;
}
pub unsafe fn l_List_singleton___redArg(
    mut v_a_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = crate::leanh::lean_box(0);
    v___x_4157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4157_, 0, v_a_4155_);
    crate::leanh::lean_ctor_set(v___x_4157_, 1, v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_List_singleton(
    mut v_00_u03b1_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = crate::leanh::lean_box(0);
    v___x_4161_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4161_, 0, v_a_4159_);
    crate::leanh::lean_ctor_set(v___x_4161_, 1, v___x_4160_);
    return v___x_4161_;
}
pub unsafe fn l_List_replicate___redArg(
    mut v_x_4162_: *mut crate::leanh::LeanObject,
    mut v_x_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4165_: u8 = 0;
    v_zero_4164_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_4165_ = lean_nat_dec_eq(v_x_4162_, v_zero_4164_);
    if v_isZero_4165_ == 1 {
        let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4163_);
        v___x_4166_ = crate::leanh::lean_box(0);
        return v___x_4166_;
    } else {
        let mut v_one_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_4167_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_4168_ = lean_nat_sub(v_x_4162_, v_one_4167_);
        crate::leanh::lean_inc(v_x_4163_);
        v___x_4169_ = l_List_replicate___redArg(v_n_4168_, v_x_4163_);
        crate::leanh::lean_dec(v_n_4168_);
        v___x_4170_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4170_, 0, v_x_4163_);
        crate::leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
        return v___x_4170_;
    }
}
pub unsafe fn l_List_replicate___redArg___boxed(
    mut v_x_4171_: *mut crate::leanh::LeanObject,
    mut v_x_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4173_ = l_List_replicate___redArg(v_x_4171_, v_x_4172_);
    crate::leanh::lean_dec(v_x_4171_);
    return v_res_4173_;
}
pub unsafe fn l_List_replicate(
    mut v_00_u03b1_4174_: *mut crate::leanh::LeanObject,
    mut v_x_4175_: *mut crate::leanh::LeanObject,
    mut v_x_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l_List_replicate___redArg(v_x_4175_, v_x_4176_);
    return v___x_4177_;
}
pub unsafe fn l_List_replicate___boxed(
    mut v_00_u03b1_4178_: *mut crate::leanh::LeanObject,
    mut v_x_4179_: *mut crate::leanh::LeanObject,
    mut v_x_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_List_replicate(v_00_u03b1_4178_, v_x_4179_, v_x_4180_);
    crate::leanh::lean_dec(v_x_4179_);
    return v_res_4181_;
}
pub unsafe fn l_List_leftpad___redArg(
    mut v_n_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
    mut v_l_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_List_length___redArg(v_l_4184_);
    v___x_4186_ = lean_nat_sub(v_n_4182_, v___x_4185_);
    crate::leanh::lean_dec(v___x_4185_);
    v___x_4187_ = l_List_replicate___redArg(v___x_4186_, v_a_4183_);
    crate::leanh::lean_dec(v___x_4186_);
    v___x_4188_ = l_List_appendTR___redArg(v___x_4187_, v_l_4184_);
    return v___x_4188_;
}
pub unsafe fn l_List_leftpad___redArg___boxed(
    mut v_n_4189_: *mut crate::leanh::LeanObject,
    mut v_a_4190_: *mut crate::leanh::LeanObject,
    mut v_l_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_List_leftpad___redArg(v_n_4189_, v_a_4190_, v_l_4191_);
    crate::leanh::lean_dec(v_n_4189_);
    return v_res_4192_;
}
pub unsafe fn l_List_leftpad(
    mut v_00_u03b1_4193_: *mut crate::leanh::LeanObject,
    mut v_n_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
    mut v_l_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_List_leftpad___redArg(v_n_4194_, v_a_4195_, v_l_4196_);
    return v___x_4197_;
}
pub unsafe fn l_List_leftpad___boxed(
    mut v_00_u03b1_4198_: *mut crate::leanh::LeanObject,
    mut v_n_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_l_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_List_leftpad(v_00_u03b1_4198_, v_n_4199_, v_a_4200_, v_l_4201_);
    crate::leanh::lean_dec(v_n_4199_);
    return v_res_4202_;
}
pub unsafe fn l_List_rightpad___redArg(
    mut v_n_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_l_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = l_List_length___redArg(v_l_4205_);
    v___x_4207_ = lean_nat_sub(v_n_4203_, v___x_4206_);
    crate::leanh::lean_dec(v___x_4206_);
    v___x_4208_ = l_List_replicate___redArg(v___x_4207_, v_a_4204_);
    crate::leanh::lean_dec(v___x_4207_);
    v___x_4209_ = l_List_appendTR___redArg(v_l_4205_, v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn l_List_rightpad___redArg___boxed(
    mut v_n_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_l_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_List_rightpad___redArg(v_n_4210_, v_a_4211_, v_l_4212_);
    crate::leanh::lean_dec(v_n_4210_);
    return v_res_4213_;
}
pub unsafe fn l_List_rightpad(
    mut v_00_u03b1_4214_: *mut crate::leanh::LeanObject,
    mut v_n_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_l_4217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_List_rightpad___redArg(v_n_4215_, v_a_4216_, v_l_4217_);
    return v___x_4218_;
}
pub unsafe fn l_List_rightpad___boxed(
    mut v_00_u03b1_4219_: *mut crate::leanh::LeanObject,
    mut v_n_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_l_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4223_ = l_List_rightpad(v_00_u03b1_4219_, v_n_4220_, v_a_4221_, v_l_4222_);
    crate::leanh::lean_dec(v_n_4220_);
    return v_res_4223_;
}
pub unsafe fn l_List_instEmptyCollection(
    mut v_00_u03b1_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = crate::leanh::lean_box(0);
    return v___x_4225_;
}
pub unsafe fn l_List_isEmpty___redArg(mut v_x_4226_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4226_) == 0 {
        let mut v___x_4227_: u8 = 0;
        v___x_4227_ = 1;
        return v___x_4227_;
    } else {
        let mut v___x_4228_: u8 = 0;
        v___x_4228_ = 0;
        return v___x_4228_;
    }
}
pub unsafe fn l_List_isEmpty___redArg___boxed(
    mut v_x_4229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4230_: u8 = 0;
    let mut v_r_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4230_ = l_List_isEmpty___redArg(v_x_4229_);
    crate::leanh::lean_dec(v_x_4229_);
    v_r_4231_ = crate::leanh::lean_box((v_res_4230_) as usize);
    return v_r_4231_;
}
pub unsafe fn l_List_isEmpty(
    mut v_00_u03b1_4232_: *mut crate::leanh::LeanObject,
    mut v_x_4233_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4234_: u8 = 0;
    v___x_4234_ = l_List_isEmpty___redArg(v_x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_List_isEmpty___boxed(
    mut v_00_u03b1_4235_: *mut crate::leanh::LeanObject,
    mut v_x_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4237_: u8 = 0;
    let mut v_r_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_List_isEmpty(v_00_u03b1_4235_, v_x_4236_);
    crate::leanh::lean_dec(v_x_4236_);
    v_r_4238_ = crate::leanh::lean_box((v_res_4237_) as usize);
    return v_r_4238_;
}
pub unsafe fn l_List_elem___redArg(
    mut v_inst_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_x_4241_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4242_: u8 = 0;
    let mut v_head_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4241_) == 0 {
                    crate::leanh::lean_dec(v_a_4240_);
                    crate::leanh::lean_dec_ref(v_inst_4239_);
                    v___x_4242_ = 0;
                    return v___x_4242_;
                } else {
                    v_head_4243_ = crate::leanh::lean_ctor_get(v_x_4241_, 0);
                    crate::leanh::lean_inc(v_head_4243_);
                    v_tail_4244_ = crate::leanh::lean_ctor_get(v_x_4241_, 1);
                    crate::leanh::lean_inc(v_tail_4244_);
                    crate::leanh::lean_dec_ref_known(v_x_4241_, 2);
                    crate::leanh::lean_inc_ref(v_inst_4239_);
                    crate::leanh::lean_inc(v_a_4240_);
                    v___x_4245_ = crate::leanh::lean_apply_2(v_inst_4239_, v_a_4240_, v_head_4243_);
                    v___x_4246_ = (crate::leanh::lean_unbox(v___x_4245_) as u8);
                    if v___x_4246_ == 0 {
                        v_x_4241_ = v_tail_4244_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4244_);
                        crate::leanh::lean_dec(v_a_4240_);
                        crate::leanh::lean_dec_ref(v_inst_4239_);
                        v___x_4248_ = (crate::leanh::lean_unbox(v___x_4245_) as u8);
                        return v___x_4248_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___redArg___boxed(
    mut v_inst_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_x_4251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4252_: u8 = 0;
    let mut v_r_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4252_ = l_List_elem___redArg(v_inst_4249_, v_a_4250_, v_x_4251_);
    v_r_4253_ = crate::leanh::lean_box((v_res_4252_) as usize);
    return v_r_4253_;
}
pub unsafe fn l_List_elem(
    mut v_00_u03b1_4254_: *mut crate::leanh::LeanObject,
    mut v_inst_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_x_4257_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4258_: u8 = 0;
    v___x_4258_ = l_List_elem___redArg(v_inst_4255_, v_a_4256_, v_x_4257_);
    return v___x_4258_;
}
pub unsafe fn l_List_elem___boxed(
    mut v_00_u03b1_4259_: *mut crate::leanh::LeanObject,
    mut v_inst_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_x_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4263_: u8 = 0;
    let mut v_r_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4263_ = l_List_elem(v_00_u03b1_4259_, v_inst_4260_, v_a_4261_, v_x_4262_);
    v_r_4264_ = crate::leanh::lean_box((v_res_4263_) as usize);
    return v_r_4264_;
}
pub unsafe fn l_List_contains___redArg(
    mut v_inst_4265_: *mut crate::leanh::LeanObject,
    mut v_as_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4268_: u8 = 0;
    v___x_4268_ = l_List_elem___redArg(v_inst_4265_, v_a_4267_, v_as_4266_);
    return v___x_4268_;
}
pub unsafe fn l_List_contains___redArg___boxed(
    mut v_inst_4269_: *mut crate::leanh::LeanObject,
    mut v_as_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4272_: u8 = 0;
    let mut v_r_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_List_contains___redArg(v_inst_4269_, v_as_4270_, v_a_4271_);
    v_r_4273_ = crate::leanh::lean_box((v_res_4272_) as usize);
    return v_r_4273_;
}
pub unsafe fn l_List_contains(
    mut v_00_u03b1_4274_: *mut crate::leanh::LeanObject,
    mut v_inst_4275_: *mut crate::leanh::LeanObject,
    mut v_as_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4278_: u8 = 0;
    v___x_4278_ = l_List_elem___redArg(v_inst_4275_, v_a_4277_, v_as_4276_);
    return v___x_4278_;
}
pub unsafe fn l_List_contains___boxed(
    mut v_00_u03b1_4279_: *mut crate::leanh::LeanObject,
    mut v_inst_4280_: *mut crate::leanh::LeanObject,
    mut v_as_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4283_: u8 = 0;
    let mut v_r_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4283_ = l_List_contains(v_00_u03b1_4279_, v_inst_4280_, v_as_4281_, v_a_4282_);
    v_r_4284_ = crate::leanh::lean_box((v_res_4283_) as usize);
    return v_r_4284_;
}
pub unsafe fn l_List_instMembership(
    mut v_00_u03b1_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = crate::leanh::lean_box(0);
    return v___x_4286_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_4287_: *mut crate::leanh::LeanObject,
    mut v_h__1_4288_: *mut crate::leanh::LeanObject,
    mut v_h__2_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4287_) == 0 {
        let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4289_);
        v___x_4290_ = crate::leanh::lean_box(0);
        v___x_4291_ = crate::leanh::lean_apply_1(v_h__1_4288_, v___x_4290_);
        return v___x_4291_;
    } else {
        let mut v_head_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4288_);
        v_head_4292_ = crate::leanh::lean_ctor_get(v_x_4287_, 0);
        crate::leanh::lean_inc(v_head_4292_);
        v_tail_4293_ = crate::leanh::lean_ctor_get(v_x_4287_, 1);
        crate::leanh::lean_inc(v_tail_4293_);
        crate::leanh::lean_dec_ref_known(v_x_4287_, 2);
        v___x_4294_ = crate::leanh::lean_apply_2(v_h__2_4289_, v_head_4292_, v_tail_4293_);
        return v___x_4294_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_4295_: *mut crate::leanh::LeanObject,
    mut v_motive_4296_: *mut crate::leanh::LeanObject,
    mut v_x_4297_: *mut crate::leanh::LeanObject,
    mut v_h__1_4298_: *mut crate::leanh::LeanObject,
    mut v_h__2_4299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4297_) == 0 {
        let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4299_);
        v___x_4300_ = crate::leanh::lean_box(0);
        v___x_4301_ = crate::leanh::lean_apply_1(v_h__1_4298_, v___x_4300_);
        return v___x_4301_;
    } else {
        let mut v_head_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4298_);
        v_head_4302_ = crate::leanh::lean_ctor_get(v_x_4297_, 0);
        crate::leanh::lean_inc(v_head_4302_);
        v_tail_4303_ = crate::leanh::lean_ctor_get(v_x_4297_, 1);
        crate::leanh::lean_inc(v_tail_4303_);
        crate::leanh::lean_dec_ref_known(v_x_4297_, 2);
        v___x_4304_ = crate::leanh::lean_apply_2(v_h__2_4299_, v_head_4302_, v_tail_4303_);
        return v___x_4304_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(
    mut v_x_4305_: u8,
    mut v_h__1_4306_: *mut crate::leanh::LeanObject,
    mut v_h__2_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_4305_ == 0 {
        let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4306_);
        v___x_4308_ = crate::leanh::lean_box(0);
        v___x_4309_ = crate::leanh::lean_apply_1(v_h__2_4307_, v___x_4308_);
        return v___x_4309_;
    } else {
        let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4307_);
        v___x_4310_ = crate::leanh::lean_box(0);
        v___x_4311_ = crate::leanh::lean_apply_1(v_h__1_4306_, v___x_4310_);
        return v___x_4311_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_4312_: *mut crate::leanh::LeanObject,
    mut v_h__1_4313_: *mut crate::leanh::LeanObject,
    mut v_h__2_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_4315_: u8 = 0;
    let mut v_res_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_4315_ = (crate::leanh::lean_unbox(v_x_4312_) as u8);
    v_res_4316_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_4315_,
        v_h__1_4313_,
        v_h__2_4314_,
    );
    return v_res_4316_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(
    mut v_motive_4317_: *mut crate::leanh::LeanObject,
    mut v_x_4318_: u8,
    mut v_h__1_4319_: *mut crate::leanh::LeanObject,
    mut v_h__2_4320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_4318_ == 0 {
        let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4319_);
        v___x_4321_ = crate::leanh::lean_box(0);
        v___x_4322_ = crate::leanh::lean_apply_1(v_h__2_4320_, v___x_4321_);
        return v___x_4322_;
    } else {
        let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4320_);
        v___x_4323_ = crate::leanh::lean_box(0);
        v___x_4324_ = crate::leanh::lean_apply_1(v_h__1_4319_, v___x_4323_);
        return v___x_4324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(
    mut v_motive_4325_: *mut crate::leanh::LeanObject,
    mut v_x_4326_: *mut crate::leanh::LeanObject,
    mut v_h__1_4327_: *mut crate::leanh::LeanObject,
    mut v_h__2_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_4329_: u8 = 0;
    let mut v_res_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_4329_ = (crate::leanh::lean_unbox(v_x_4326_) as u8);
    v_res_4330_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(
        v_motive_4325_,
        v_x_37__boxed_4329_,
        v_h__1_4327_,
        v_h__2_4328_,
    );
    return v_res_4330_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___redArg(
    mut v_inst_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
    mut v_as_4333_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4334_: u8 = 0;
    v___x_4334_ = l_List_elem___redArg(v_inst_4331_, v_a_4332_, v_as_4333_);
    return v___x_4334_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___redArg___boxed(
    mut v_inst_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_as_4337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4338_: u8 = 0;
    let mut v_r_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_4335_, v_a_4336_, v_as_4337_);
    v_r_4339_ = crate::leanh::lean_box((v_res_4338_) as usize);
    return v_r_4339_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq(
    mut v_00_u03b1_4340_: *mut crate::leanh::LeanObject,
    mut v_inst_4341_: *mut crate::leanh::LeanObject,
    mut v_inst_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_as_4344_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4345_: u8 = 0;
    v___x_4345_ = l_List_elem___redArg(v_inst_4341_, v_a_4343_, v_as_4344_);
    return v___x_4345_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___boxed(
    mut v_00_u03b1_4346_: *mut crate::leanh::LeanObject,
    mut v_inst_4347_: *mut crate::leanh::LeanObject,
    mut v_inst_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_as_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4351_: u8 = 0;
    let mut v_r_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4351_ = l_List_instDecidableMemOfLawfulBEq(
        v_00_u03b1_4346_,
        v_inst_4347_,
        v_inst_4348_,
        v_a_4349_,
        v_as_4350_,
    );
    v_r_4352_ = crate::leanh::lean_box((v_res_4351_) as usize);
    return v_r_4352_;
}
pub unsafe fn l_List_decidableBEx___redArg(
    mut v_inst_4353_: *mut crate::leanh::LeanObject,
    mut v_x_4354_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4355_: u8 = 0;
    let mut v_head_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4354_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4353_);
                    v___x_4355_ = 0;
                    return v___x_4355_;
                } else {
                    v_head_4356_ = crate::leanh::lean_ctor_get(v_x_4354_, 0);
                    crate::leanh::lean_inc(v_head_4356_);
                    v_tail_4357_ = crate::leanh::lean_ctor_get(v_x_4354_, 1);
                    crate::leanh::lean_inc(v_tail_4357_);
                    crate::leanh::lean_dec_ref_known(v_x_4354_, 2);
                    crate::leanh::lean_inc_ref(v_inst_4353_);
                    v___x_4358_ = crate::leanh::lean_apply_1(v_inst_4353_, v_head_4356_);
                    v___x_4359_ = (crate::leanh::lean_unbox(v___x_4358_) as u8);
                    if v___x_4359_ == 0 {
                        v_x_4354_ = v_tail_4357_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_4357_);
                        crate::leanh::lean_dec_ref(v_inst_4353_);
                        v___x_4361_ = (crate::leanh::lean_unbox(v___x_4358_) as u8);
                        return v___x_4361_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_decidableBEx___redArg___boxed(
    mut v_inst_4362_: *mut crate::leanh::LeanObject,
    mut v_x_4363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4364_: u8 = 0;
    let mut v_r_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4364_ = l_List_decidableBEx___redArg(v_inst_4362_, v_x_4363_);
    v_r_4365_ = crate::leanh::lean_box((v_res_4364_) as usize);
    return v_r_4365_;
}
pub unsafe fn l_List_decidableBEx(
    mut v_00_u03b1_4366_: *mut crate::leanh::LeanObject,
    mut v_p_4367_: *mut crate::leanh::LeanObject,
    mut v_inst_4368_: *mut crate::leanh::LeanObject,
    mut v_x_4369_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4370_: u8 = 0;
    v___x_4370_ = l_List_decidableBEx___redArg(v_inst_4368_, v_x_4369_);
    return v___x_4370_;
}
pub unsafe fn l_List_decidableBEx___boxed(
    mut v_00_u03b1_4371_: *mut crate::leanh::LeanObject,
    mut v_p_4372_: *mut crate::leanh::LeanObject,
    mut v_inst_4373_: *mut crate::leanh::LeanObject,
    mut v_x_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4375_: u8 = 0;
    let mut v_r_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_List_decidableBEx(v_00_u03b1_4371_, v_p_4372_, v_inst_4373_, v_x_4374_);
    v_r_4376_ = crate::leanh::lean_box((v_res_4375_) as usize);
    return v_r_4376_;
}
pub unsafe fn l_List_decidableBAll___redArg(
    mut v_inst_4377_: *mut crate::leanh::LeanObject,
    mut v_x_4378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4379_: u8 = 0;
    let mut v_head_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4378_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4377_);
                    v___x_4379_ = 1;
                    return v___x_4379_;
                } else {
                    v_head_4380_ = crate::leanh::lean_ctor_get(v_x_4378_, 0);
                    crate::leanh::lean_inc(v_head_4380_);
                    v_tail_4381_ = crate::leanh::lean_ctor_get(v_x_4378_, 1);
                    crate::leanh::lean_inc(v_tail_4381_);
                    crate::leanh::lean_dec_ref_known(v_x_4378_, 2);
                    crate::leanh::lean_inc_ref(v_inst_4377_);
                    v___x_4382_ = crate::leanh::lean_apply_1(v_inst_4377_, v_head_4380_);
                    v___x_4383_ = (crate::leanh::lean_unbox(v___x_4382_) as u8);
                    if v___x_4383_ == 0 {
                        crate::leanh::lean_dec(v_tail_4381_);
                        crate::leanh::lean_dec_ref(v_inst_4377_);
                        v___x_4384_ = (crate::leanh::lean_unbox(v___x_4382_) as u8);
                        return v___x_4384_;
                    } else {
                        v_x_4378_ = v_tail_4381_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_decidableBAll___redArg___boxed(
    mut v_inst_4386_: *mut crate::leanh::LeanObject,
    mut v_x_4387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4388_: u8 = 0;
    let mut v_r_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4388_ = l_List_decidableBAll___redArg(v_inst_4386_, v_x_4387_);
    v_r_4389_ = crate::leanh::lean_box((v_res_4388_) as usize);
    return v_r_4389_;
}
pub unsafe fn l_List_decidableBAll(
    mut v_00_u03b1_4390_: *mut crate::leanh::LeanObject,
    mut v_p_4391_: *mut crate::leanh::LeanObject,
    mut v_inst_4392_: *mut crate::leanh::LeanObject,
    mut v_x_4393_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4394_: u8 = 0;
    v___x_4394_ = l_List_decidableBAll___redArg(v_inst_4392_, v_x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_List_decidableBAll___boxed(
    mut v_00_u03b1_4395_: *mut crate::leanh::LeanObject,
    mut v_p_4396_: *mut crate::leanh::LeanObject,
    mut v_inst_4397_: *mut crate::leanh::LeanObject,
    mut v_x_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4399_: u8 = 0;
    let mut v_r_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ = l_List_decidableBAll(v_00_u03b1_4395_, v_p_4396_, v_inst_4397_, v_x_4398_);
    v_r_4400_ = crate::leanh::lean_box((v_res_4399_) as usize);
    return v_r_4400_;
}
pub unsafe fn l_List_take___redArg(
    mut v_x_4401_: *mut crate::leanh::LeanObject,
    mut v_x_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4404_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v_one_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4403_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4404_ = lean_nat_dec_eq(v_x_4401_, v_zero_4403_);
                if v_isZero_4404_ == 1 {
                    crate::leanh::lean_dec(v_x_4402_);
                    v___x_4405_ = crate::leanh::lean_box(0);
                    return v___x_4405_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4402_) == 0 {
                        return v_x_4402_;
                    } else {
                        v_head_4406_ = crate::leanh::lean_ctor_get(v_x_4402_, 0);
                        v_tail_4407_ = crate::leanh::lean_ctor_get(v_x_4402_, 1);
                        v_isSharedCheck_4417_ = (!crate::leanh::lean_is_exclusive(v_x_4402_)) as u8;
                        if v_isSharedCheck_4417_ == 0 {
                            v___x_4409_ = v_x_4402_;
                            v_isShared_4410_ = v_isSharedCheck_4417_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_4407_);
                            crate::leanh::lean_inc(v_head_4406_);
                            crate::leanh::lean_dec(v_x_4402_);
                            v___x_4409_ = crate::leanh::lean_box(0);
                            v_isShared_4410_ = v_isSharedCheck_4417_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_4411_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_4412_ = lean_nat_sub(v_x_4401_, v_one_4411_);
                v___x_4413_ = l_List_take___redArg(v_n_4412_, v_tail_4407_);
                crate::leanh::lean_dec(v_n_4412_);
                if v_isShared_4410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4409_, 1, v___x_4413_);
                    v___x_4415_ = v___x_4409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_head_4406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4413_);
                    v___x_4415_ = v_reuseFailAlloc_4416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_take___redArg___boxed(
    mut v_x_4418_: *mut crate::leanh::LeanObject,
    mut v_x_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4420_ = l_List_take___redArg(v_x_4418_, v_x_4419_);
    crate::leanh::lean_dec(v_x_4418_);
    return v_res_4420_;
}
pub unsafe fn l_List_take(
    mut v_00_u03b1_4421_: *mut crate::leanh::LeanObject,
    mut v_x_4422_: *mut crate::leanh::LeanObject,
    mut v_x_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4424_ = l_List_take___redArg(v_x_4422_, v_x_4423_);
    return v___x_4424_;
}
pub unsafe fn l_List_take___boxed(
    mut v_00_u03b1_4425_: *mut crate::leanh::LeanObject,
    mut v_x_4426_: *mut crate::leanh::LeanObject,
    mut v_x_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_List_take(v_00_u03b1_4425_, v_x_4426_, v_x_4427_);
    crate::leanh::lean_dec(v_x_4426_);
    return v_res_4428_;
}
pub unsafe fn l_List_drop___redArg(
    mut v_x_4429_: *mut crate::leanh::LeanObject,
    mut v_x_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4432_: u8 = 0;
    let mut v_tail_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4431_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4432_ = lean_nat_dec_eq(v_x_4429_, v_zero_4431_);
                if v_isZero_4432_ == 1 {
                    crate::leanh::lean_dec(v_x_4429_);
                    crate::leanh::lean_inc(v_x_4430_);
                    return v_x_4430_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4430_) == 0 {
                        crate::leanh::lean_dec(v_x_4429_);
                        return v_x_4430_;
                    } else {
                        v_tail_4433_ = crate::leanh::lean_ctor_get(v_x_4430_, 1);
                        v_one_4434_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_4435_ = lean_nat_sub(v_x_4429_, v_one_4434_);
                        crate::leanh::lean_dec(v_x_4429_);
                        v_x_4429_ = v_n_4435_;
                        v_x_4430_ = v_tail_4433_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_drop___redArg___boxed(
    mut v_x_4437_: *mut crate::leanh::LeanObject,
    mut v_x_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_List_drop___redArg(v_x_4437_, v_x_4438_);
    crate::leanh::lean_dec(v_x_4438_);
    return v_res_4439_;
}
pub unsafe fn l_List_drop(
    mut v_00_u03b1_4440_: *mut crate::leanh::LeanObject,
    mut v_x_4441_: *mut crate::leanh::LeanObject,
    mut v_x_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_List_drop___redArg(v_x_4441_, v_x_4442_);
    return v___x_4443_;
}
pub unsafe fn l_List_drop___boxed(
    mut v_00_u03b1_4444_: *mut crate::leanh::LeanObject,
    mut v_x_4445_: *mut crate::leanh::LeanObject,
    mut v_x_4446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4447_ = l_List_drop(v_00_u03b1_4444_, v_x_4445_, v_x_4446_);
    crate::leanh::lean_dec(v_x_4446_);
    return v_res_4447_;
}
pub unsafe fn l_List_extract___redArg(
    mut v_l_4448_: *mut crate::leanh::LeanObject,
    mut v_start_4449_: *mut crate::leanh::LeanObject,
    mut v_stop_4450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = lean_nat_sub(v_stop_4450_, v_start_4449_);
    v___x_4452_ = l_List_drop___redArg(v_start_4449_, v_l_4448_);
    v___x_4453_ = l_List_take___redArg(v___x_4451_, v___x_4452_);
    crate::leanh::lean_dec(v___x_4451_);
    return v___x_4453_;
}
pub unsafe fn l_List_extract___redArg___boxed(
    mut v_l_4454_: *mut crate::leanh::LeanObject,
    mut v_start_4455_: *mut crate::leanh::LeanObject,
    mut v_stop_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_List_extract___redArg(v_l_4454_, v_start_4455_, v_stop_4456_);
    crate::leanh::lean_dec(v_stop_4456_);
    crate::leanh::lean_dec(v_l_4454_);
    return v_res_4457_;
}
pub unsafe fn l_List_extract(
    mut v_00_u03b1_4458_: *mut crate::leanh::LeanObject,
    mut v_l_4459_: *mut crate::leanh::LeanObject,
    mut v_start_4460_: *mut crate::leanh::LeanObject,
    mut v_stop_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4462_ = lean_nat_sub(v_stop_4461_, v_start_4460_);
    v___x_4463_ = l_List_drop___redArg(v_start_4460_, v_l_4459_);
    v___x_4464_ = l_List_take___redArg(v___x_4462_, v___x_4463_);
    crate::leanh::lean_dec(v___x_4462_);
    return v___x_4464_;
}
pub unsafe fn l_List_extract___boxed(
    mut v_00_u03b1_4465_: *mut crate::leanh::LeanObject,
    mut v_l_4466_: *mut crate::leanh::LeanObject,
    mut v_start_4467_: *mut crate::leanh::LeanObject,
    mut v_stop_4468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = l_List_extract(v_00_u03b1_4465_, v_l_4466_, v_start_4467_, v_stop_4468_);
    crate::leanh::lean_dec(v_stop_4468_);
    crate::leanh::lean_dec(v_l_4466_);
    return v_res_4469_;
}
pub unsafe fn l_List_takeWhile___redArg(
    mut v_p_4470_: *mut crate::leanh::LeanObject,
    mut v_x_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4471_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_4470_);
                    return v_x_4471_;
                } else {
                    v_head_4472_ = crate::leanh::lean_ctor_get(v_x_4471_, 0);
                    v_tail_4473_ = crate::leanh::lean_ctor_get(v_x_4471_, 1);
                    v_isSharedCheck_4484_ = (!crate::leanh::lean_is_exclusive(v_x_4471_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4475_ = v_x_4471_;
                        v_isShared_4476_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4473_);
                        crate::leanh::lean_inc(v_head_4472_);
                        crate::leanh::lean_dec(v_x_4471_);
                        v___x_4475_ = crate::leanh::lean_box(0);
                        v_isShared_4476_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_p_4470_);
                crate::leanh::lean_inc(v_head_4472_);
                v___x_4477_ = crate::leanh::lean_apply_1(v_p_4470_, v_head_4472_);
                v___x_4478_ = (crate::leanh::lean_unbox(v___x_4477_) as u8);
                if v___x_4478_ == 0 {
                    crate::leanh::lean_del_object(v___x_4475_);
                    crate::leanh::lean_dec(v_tail_4473_);
                    crate::leanh::lean_dec(v_head_4472_);
                    crate::leanh::lean_dec_ref(v_p_4470_);
                    v___x_4479_ = crate::leanh::lean_box(0);
                    return v___x_4479_;
                } else {
                    v___x_4480_ = l_List_takeWhile___redArg(v_p_4470_, v_tail_4473_);
                    if v_isShared_4476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4475_, 1, v___x_4480_);
                        v___x_4482_ = v___x_4475_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_head_4472_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___x_4480_);
                        v___x_4482_ = v_reuseFailAlloc_4483_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_takeWhile(
    mut v_00_u03b1_4485_: *mut crate::leanh::LeanObject,
    mut v_p_4486_: *mut crate::leanh::LeanObject,
    mut v_x_4487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = l_List_takeWhile___redArg(v_p_4486_, v_x_4487_);
    return v___x_4488_;
}
pub unsafe fn l_List_dropWhile___redArg(
    mut v_p_4489_: *mut crate::leanh::LeanObject,
    mut v_x_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4490_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_4489_);
                    return v_x_4490_;
                } else {
                    v_head_4491_ = crate::leanh::lean_ctor_get(v_x_4490_, 0);
                    v_tail_4492_ = crate::leanh::lean_ctor_get(v_x_4490_, 1);
                    crate::leanh::lean_inc_ref(v_p_4489_);
                    crate::leanh::lean_inc(v_head_4491_);
                    v___x_4493_ = crate::leanh::lean_apply_1(v_p_4489_, v_head_4491_);
                    v___x_4494_ = (crate::leanh::lean_unbox(v___x_4493_) as u8);
                    if v___x_4494_ == 0 {
                        crate::leanh::lean_dec_ref(v_p_4489_);
                        return v_x_4490_;
                    } else {
                        crate::leanh::lean_inc(v_tail_4492_);
                        crate::leanh::lean_dec_ref_known(v_x_4490_, 2);
                        v_x_4490_ = v_tail_4492_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_dropWhile(
    mut v_00_u03b1_4496_: *mut crate::leanh::LeanObject,
    mut v_p_4497_: *mut crate::leanh::LeanObject,
    mut v_x_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4499_ = l_List_dropWhile___redArg(v_p_4497_, v_x_4498_);
    return v___x_4499_;
}
pub unsafe fn l_List_partition_loop___redArg(
    mut v_p_4500_: *mut crate::leanh::LeanObject,
    mut v_a_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_head_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v_fst_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_isSharedCheck_4541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4501_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_4500_);
                    v_fst_4503_ = crate::leanh::lean_ctor_get(v_a_4502_, 0);
                    v_snd_4504_ = crate::leanh::lean_ctor_get(v_a_4502_, 1);
                    v_isSharedCheck_4513_ = (!crate::leanh::lean_is_exclusive(v_a_4502_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4506_ = v_a_4502_;
                        v_isShared_4507_ = v_isSharedCheck_4513_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4504_);
                        crate::leanh::lean_inc(v_fst_4503_);
                        crate::leanh::lean_dec(v_a_4502_);
                        v___x_4506_ = crate::leanh::lean_box(0);
                        v_isShared_4507_ = v_isSharedCheck_4513_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_4514_ = crate::leanh::lean_ctor_get(v_a_4501_, 0);
                    v_tail_4515_ = crate::leanh::lean_ctor_get(v_a_4501_, 1);
                    v_isSharedCheck_4541_ = (!crate::leanh::lean_is_exclusive(v_a_4501_)) as u8;
                    if v_isSharedCheck_4541_ == 0 {
                        v___x_4517_ = v_a_4501_;
                        v_isShared_4518_ = v_isSharedCheck_4541_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4515_);
                        crate::leanh::lean_inc(v_head_4514_);
                        crate::leanh::lean_dec(v_a_4501_);
                        v___x_4517_ = crate::leanh::lean_box(0);
                        v_isShared_4518_ = v_isSharedCheck_4541_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4508_ = l_List_reverse___redArg(v_fst_4503_);
                v___x_4509_ = l_List_reverse___redArg(v_snd_4504_);
                if v_isShared_4507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4506_, 1, v___x_4509_);
                    crate::leanh::lean_ctor_set(v___x_4506_, 0, v___x_4508_);
                    v___x_4511_ = v___x_4506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 1, v___x_4509_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4511_;
            }
            3 => {
                v_fst_4519_ = crate::leanh::lean_ctor_get(v_a_4502_, 0);
                v_snd_4520_ = crate::leanh::lean_ctor_get(v_a_4502_, 1);
                v_isSharedCheck_4540_ = (!crate::leanh::lean_is_exclusive(v_a_4502_)) as u8;
                if v_isSharedCheck_4540_ == 0 {
                    v___x_4522_ = v_a_4502_;
                    v_isShared_4523_ = v_isSharedCheck_4540_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4520_);
                    crate::leanh::lean_inc(v_fst_4519_);
                    crate::leanh::lean_dec(v_a_4502_);
                    v___x_4522_ = crate::leanh::lean_box(0);
                    v_isShared_4523_ = v_isSharedCheck_4540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_p_4500_);
                crate::leanh::lean_inc(v_head_4514_);
                v___x_4524_ = crate::leanh::lean_apply_1(v_p_4500_, v_head_4514_);
                v___x_4525_ = (crate::leanh::lean_unbox(v___x_4524_) as u8);
                if v___x_4525_ == 0 {
                    if v_isShared_4518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4517_, 1, v_snd_4520_);
                        v___x_4527_ = v___x_4517_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4532_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_head_4514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_snd_4520_);
                        v___x_4527_ = v_reuseFailAlloc_4532_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4517_, 1, v_fst_4519_);
                        v___x_4534_ = v___x_4517_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4539_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_head_4514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_fst_4519_);
                        v___x_4534_ = v_reuseFailAlloc_4539_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4522_, 1, v___x_4527_);
                    v___x_4529_ = v___x_4522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_fst_4519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___x_4527_);
                    v___x_4529_ = v_reuseFailAlloc_4531_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4501_ = v_tail_4515_;
                v_a_4502_ = v___x_4529_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_4523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4522_, 0, v___x_4534_);
                    v___x_4536_ = v___x_4522_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_snd_4520_);
                    v___x_4536_ = v_reuseFailAlloc_4538_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4501_ = v_tail_4515_;
                v_a_4502_ = v___x_4536_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_partition_loop(
    mut v_00_u03b1_4542_: *mut crate::leanh::LeanObject,
    mut v_p_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_List_partition_loop___redArg(v_p_4543_, v_a_4544_, v_a_4545_);
    return v___x_4546_;
}
pub unsafe fn l_List_partition___redArg(
    mut v_p_4549_: *mut crate::leanh::LeanObject,
    mut v_as_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_List_partition___redArg___closed__0;
    v___x_4552_ = l_List_partition_loop___redArg(v_p_4549_, v_as_4550_, v___x_4551_);
    return v___x_4552_;
}
pub unsafe fn l_List_partition(
    mut v_00_u03b1_4553_: *mut crate::leanh::LeanObject,
    mut v_p_4554_: *mut crate::leanh::LeanObject,
    mut v_as_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_List_partition___redArg___closed__0;
    v___x_4557_ = l_List_partition_loop___redArg(v_p_4554_, v_as_4555_, v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn l_List_dropLast___redArg(
    mut v_x_4558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_unused_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4558_) == 0 {
                    return v_x_4558_;
                } else {
                    v_tail_4559_ = crate::leanh::lean_ctor_get(v_x_4558_, 1);
                    crate::leanh::lean_inc(v_tail_4559_);
                    if crate::leanh::lean_obj_tag(v_tail_4559_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_4558_, 2);
                        return v_tail_4559_;
                    } else {
                        v_head_4560_ = crate::leanh::lean_ctor_get(v_x_4558_, 0);
                        v_isSharedCheck_4568_ = (!crate::leanh::lean_is_exclusive(v_x_4558_)) as u8;
                        if v_isSharedCheck_4568_ == 0 {
                            v_unused_4569_ = crate::leanh::lean_ctor_get(v_x_4558_, 1);
                            crate::leanh::lean_dec(v_unused_4569_);
                            v___x_4562_ = v_x_4558_;
                            v_isShared_4563_ = v_isSharedCheck_4568_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_4560_);
                            crate::leanh::lean_dec(v_x_4558_);
                            v___x_4562_ = crate::leanh::lean_box(0);
                            v_isShared_4563_ = v_isSharedCheck_4568_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4564_ = l_List_dropLast___redArg(v_tail_4559_);
                if v_isShared_4563_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4562_, 1, v___x_4564_);
                    v___x_4566_ = v___x_4562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_head_4560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 1, v___x_4564_);
                    v___x_4566_ = v_reuseFailAlloc_4567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_dropLast(
    mut v_00_u03b1_4570_: *mut crate::leanh::LeanObject,
    mut v_x_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = l_List_dropLast___redArg(v_x_4571_);
    return v___x_4572_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(
    mut v_x_4573_: *mut crate::leanh::LeanObject,
    mut v_h__1_4574_: *mut crate::leanh::LeanObject,
    mut v_h__2_4575_: *mut crate::leanh::LeanObject,
    mut v_h__3_4576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4573_) == 0 {
        let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4576_);
        crate::leanh::lean_dec(v_h__2_4575_);
        v___x_4577_ = crate::leanh::lean_box(0);
        v___x_4578_ = crate::leanh::lean_apply_1(v_h__1_4574_, v___x_4577_);
        return v___x_4578_;
    } else {
        let mut v_tail_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4574_);
        v_tail_4579_ = crate::leanh::lean_ctor_get(v_x_4573_, 1);
        if crate::leanh::lean_obj_tag(v_tail_4579_) == 0 {
            let mut v_head_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4576_);
            v_head_4580_ = crate::leanh::lean_ctor_get(v_x_4573_, 0);
            crate::leanh::lean_inc(v_head_4580_);
            crate::leanh::lean_dec_ref_known(v_x_4573_, 2);
            v___x_4581_ = crate::leanh::lean_apply_1(v_h__2_4575_, v_head_4580_);
            return v___x_4581_;
        } else {
            let mut v_head_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_4579_);
            crate::leanh::lean_dec(v_h__2_4575_);
            v_head_4582_ = crate::leanh::lean_ctor_get(v_x_4573_, 0);
            crate::leanh::lean_inc(v_head_4582_);
            crate::leanh::lean_dec_ref_known(v_x_4573_, 2);
            v___x_4583_ = crate::leanh::lean_apply_3(
                v_h__3_4576_,
                v_head_4582_,
                v_tail_4579_,
                crate::leanh::lean_box(0),
            );
            return v___x_4583_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(
    mut v_00_u03b1_4584_: *mut crate::leanh::LeanObject,
    mut v_motive_4585_: *mut crate::leanh::LeanObject,
    mut v_x_4586_: *mut crate::leanh::LeanObject,
    mut v_h__1_4587_: *mut crate::leanh::LeanObject,
    mut v_h__2_4588_: *mut crate::leanh::LeanObject,
    mut v_h__3_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4586_) == 0 {
        let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4589_);
        crate::leanh::lean_dec(v_h__2_4588_);
        v___x_4590_ = crate::leanh::lean_box(0);
        v___x_4591_ = crate::leanh::lean_apply_1(v_h__1_4587_, v___x_4590_);
        return v___x_4591_;
    } else {
        let mut v_tail_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4587_);
        v_tail_4592_ = crate::leanh::lean_ctor_get(v_x_4586_, 1);
        if crate::leanh::lean_obj_tag(v_tail_4592_) == 0 {
            let mut v_head_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4589_);
            v_head_4593_ = crate::leanh::lean_ctor_get(v_x_4586_, 0);
            crate::leanh::lean_inc(v_head_4593_);
            crate::leanh::lean_dec_ref_known(v_x_4586_, 2);
            v___x_4594_ = crate::leanh::lean_apply_1(v_h__2_4588_, v_head_4593_);
            return v___x_4594_;
        } else {
            let mut v_head_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_4592_);
            crate::leanh::lean_dec(v_h__2_4588_);
            v_head_4595_ = crate::leanh::lean_ctor_get(v_x_4586_, 0);
            crate::leanh::lean_inc(v_head_4595_);
            crate::leanh::lean_dec_ref_known(v_x_4586_, 2);
            v___x_4596_ = crate::leanh::lean_apply_3(
                v_h__3_4589_,
                v_head_4595_,
                v_tail_4592_,
                crate::leanh::lean_box(0),
            );
            return v___x_4596_;
        }
    }
}
pub unsafe fn l_List_instHasSubset(
    mut v_00_u03b1_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4598_ = crate::leanh::lean_box(0);
    return v___x_4598_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(
    mut v___f_4599_: *mut crate::leanh::LeanObject,
    mut v_x_4600_: *mut crate::leanh::LeanObject,
    mut v_a_4601_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4602_: u8 = 0;
    v___x_4602_ = l_List_elem___redArg(v___f_4599_, v_a_4601_, v_x_4600_);
    return v___x_4602_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(
    mut v___f_4603_: *mut crate::leanh::LeanObject,
    mut v_x_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4606_: u8 = 0;
    let mut v_r_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(
        v___f_4603_,
        v_x_4604_,
        v_a_4605_,
    );
    v_r_4607_ = crate::leanh::lean_box((v_res_4606_) as usize);
    return v_r_4607_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg(
    mut v_inst_4608_: *mut crate::leanh::LeanObject,
    mut v_x_4609_: *mut crate::leanh::LeanObject,
    mut v_x_4610_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    v___f_4611_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4611_, 0, v_inst_4608_);
    v___f_4612_ = crate::leanh::lean_alloc_closure(
        l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4612_, 0, v___f_4611_);
    crate::leanh::lean_closure_set(v___f_4612_, 1, v_x_4610_);
    v___x_4613_ = l_List_decidableBAll___redArg(v___f_4612_, v_x_4609_);
    return v___x_4613_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(
    mut v_inst_4614_: *mut crate::leanh::LeanObject,
    mut v_x_4615_: *mut crate::leanh::LeanObject,
    mut v_x_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4617_: u8 = 0;
    let mut v_r_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ =
        l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_4614_, v_x_4615_, v_x_4616_);
    v_r_4618_ = crate::leanh::lean_box((v_res_4617_) as usize);
    return v_r_4618_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq(
    mut v_00_u03b1_4619_: *mut crate::leanh::LeanObject,
    mut v_inst_4620_: *mut crate::leanh::LeanObject,
    mut v_x_4621_: *mut crate::leanh::LeanObject,
    mut v_x_4622_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4623_: u8 = 0;
    v___x_4623_ =
        l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_4620_, v_x_4621_, v_x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___boxed(
    mut v_00_u03b1_4624_: *mut crate::leanh::LeanObject,
    mut v_inst_4625_: *mut crate::leanh::LeanObject,
    mut v_x_4626_: *mut crate::leanh::LeanObject,
    mut v_x_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4628_: u8 = 0;
    let mut v_r_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_List_instDecidableRelSubsetOfDecidableEq(
        v_00_u03b1_4624_,
        v_inst_4625_,
        v_x_4626_,
        v_x_4627_,
    );
    v_r_4629_ = crate::leanh::lean_box((v_res_4628_) as usize);
    return v_r_4629_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2;
    v___x_4664_ = l_String_toRawSubstring_x27(v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(
    mut v_x_4684_: *mut crate::leanh::LeanObject,
    mut v_a_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    v___x_4687_ = l_List_term___x3c_x2b___00__closed__2;
    crate::leanh::lean_inc(v_x_4684_);
    v___x_4688_ = l_Lean_Syntax_isOfKind(v_x_4684_, v___x_4687_);
    if v___x_4688_ == 0 {
        let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4684_);
        v___x_4689_ = crate::leanh::lean_box(1);
        v___x_4690_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
        crate::leanh::lean_ctor_set(v___x_4690_, 1, v_a_4686_);
        return v___x_4690_;
    } else {
        let mut v_quotContext_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4698_: u8 = 0;
        let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4691_ = crate::leanh::lean_ctor_get(v_a_4685_, 1);
        v_currMacroScope_4692_ = crate::leanh::lean_ctor_get(v_a_4685_, 2);
        v_ref_4693_ = crate::leanh::lean_ctor_get(v_a_4685_, 5);
        v___x_4694_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4695_ = l_Lean_Syntax_getArg(v_x_4684_, v___x_4694_);
        v___x_4696_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4697_ = l_Lean_Syntax_getArg(v_x_4684_, v___x_4696_);
        crate::leanh::lean_dec(v_x_4684_);
        v___x_4698_ = 0;
        v___x_4699_ = l_Lean_SourceInfo_fromRef(v_ref_4693_, v___x_4698_);
        v___x_4700_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_4701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
        v___x_4702_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4;
        crate::leanh::lean_inc(v_currMacroScope_4692_);
        crate::leanh::lean_inc(v_quotContext_4691_);
        v___x_4703_ =
            l_Lean_addMacroScope(v_quotContext_4691_, v___x_4702_, v_currMacroScope_4692_);
        v___x_4704_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10;
        crate::leanh::lean_inc_n(v___x_4699_, 2);
        v___x_4705_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4705_, 0, v___x_4699_);
        crate::leanh::lean_ctor_set(v___x_4705_, 1, v___x_4701_);
        crate::leanh::lean_ctor_set(v___x_4705_, 2, v___x_4703_);
        crate::leanh::lean_ctor_set(v___x_4705_, 3, v___x_4704_);
        v___x_4706_ = l_List_lex___auto__1___closed__9;
        v___x_4707_ = l_Lean_Syntax_node2(v___x_4699_, v___x_4706_, v___x_4695_, v___x_4697_);
        v___x_4708_ = l_Lean_Syntax_node2(v___x_4699_, v___x_4700_, v___x_4705_, v___x_4707_);
        v___x_4709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4709_, 0, v___x_4708_);
        crate::leanh::lean_ctor_set(v___x_4709_, 1, v_a_4686_);
        return v___x_4709_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(
    mut v_x_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4713_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(
        v_x_4710_, v_a_4711_, v_a_4712_,
    );
    crate::leanh::lean_dec_ref(v_a_4711_);
    return v_res_4713_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(
    mut v_x_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: u8 = 0;
    v___x_4720_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    crate::leanh::lean_inc(v_x_4717_);
    v___x_4721_ = l_Lean_Syntax_isOfKind(v_x_4717_, v___x_4720_);
    if v___x_4721_ == 0 {
        let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4717_);
        v___x_4722_ = crate::leanh::lean_box(0);
        v___x_4723_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4723_, 0, v___x_4722_);
        crate::leanh::lean_ctor_set(v___x_4723_, 1, v_a_4719_);
        return v___x_4723_;
    } else {
        let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: u8 = 0;
        v___x_4724_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4725_ = l_Lean_Syntax_getArg(v_x_4717_, v___x_4724_);
        v___x_4726_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        crate::leanh::lean_inc(v___x_4725_);
        v___x_4727_ = l_Lean_Syntax_isOfKind(v___x_4725_, v___x_4726_);
        if v___x_4727_ == 0 {
            let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4725_);
            crate::leanh::lean_dec(v_x_4717_);
            v___x_4728_ = crate::leanh::lean_box(0);
            v___x_4729_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4729_, 0, v___x_4728_);
            crate::leanh::lean_ctor_set(v___x_4729_, 1, v_a_4719_);
            return v___x_4729_;
        } else {
            let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4733_: u8 = 0;
            v___x_4730_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4731_ = l_Lean_Syntax_getArg(v_x_4717_, v___x_4730_);
            crate::leanh::lean_dec(v_x_4717_);
            v___x_4732_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_4731_);
            v___x_4733_ = l_Lean_Syntax_matchesNull(v___x_4731_, v___x_4732_);
            if v___x_4733_ == 0 {
                let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4731_);
                crate::leanh::lean_dec(v___x_4725_);
                v___x_4734_ = crate::leanh::lean_box(0);
                v___x_4735_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4735_, 0, v___x_4734_);
                crate::leanh::lean_ctor_set(v___x_4735_, 1, v_a_4719_);
                return v___x_4735_;
            } else {
                let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4739_: u8 = 0;
                let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4736_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4724_);
                v___x_4737_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4730_);
                crate::leanh::lean_dec(v___x_4731_);
                v_ref_4738_ = l_Lean_replaceRef(v___x_4725_, v_a_4718_);
                crate::leanh::lean_dec(v___x_4725_);
                v___x_4739_ = 0;
                v___x_4740_ = l_Lean_SourceInfo_fromRef(v_ref_4738_, v___x_4739_);
                crate::leanh::lean_dec(v_ref_4738_);
                v___x_4741_ = l_List_term___x3c_x2b___00__closed__2;
                v___x_4742_ = l_List_term___x3c_x2b___00__closed__5;
                crate::leanh::lean_inc(v___x_4740_);
                v___x_4743_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4740_);
                crate::leanh::lean_ctor_set(v___x_4743_, 1, v___x_4742_);
                v___x_4744_ = l_Lean_Syntax_node3(
                    v___x_4740_,
                    v___x_4741_,
                    v___x_4736_,
                    v___x_4743_,
                    v___x_4737_,
                );
                v___x_4745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4745_, 0, v___x_4744_);
                crate::leanh::lean_ctor_set(v___x_4745_, 1, v_a_4719_);
                return v___x_4745_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(
    mut v_x_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4749_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(
        v_x_4746_, v_a_4747_, v_a_4748_,
    );
    crate::leanh::lean_dec(v_a_4747_);
    return v_res_4749_;
}
pub unsafe fn l_List_isSublist___redArg(
    mut v_inst_4750_: *mut crate::leanh::LeanObject,
    mut v_x_4751_: *mut crate::leanh::LeanObject,
    mut v_x_4752_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: u8 = 0;
    let mut v_head_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4751_) == 0 {
                    crate::leanh::lean_dec(v_x_4752_);
                    crate::leanh::lean_dec_ref(v_inst_4750_);
                    v___x_4753_ = 1;
                    return v___x_4753_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4752_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_4751_, 2);
                        crate::leanh::lean_dec_ref(v_inst_4750_);
                        v___x_4754_ = 0;
                        return v___x_4754_;
                    } else {
                        v_head_4755_ = crate::leanh::lean_ctor_get(v_x_4751_, 0);
                        v_tail_4756_ = crate::leanh::lean_ctor_get(v_x_4751_, 1);
                        v_head_4757_ = crate::leanh::lean_ctor_get(v_x_4752_, 0);
                        crate::leanh::lean_inc(v_head_4757_);
                        v_tail_4758_ = crate::leanh::lean_ctor_get(v_x_4752_, 1);
                        crate::leanh::lean_inc(v_tail_4758_);
                        crate::leanh::lean_dec_ref_known(v_x_4752_, 2);
                        crate::leanh::lean_inc_ref(v_inst_4750_);
                        crate::leanh::lean_inc(v_head_4755_);
                        v___x_4759_ =
                            crate::leanh::lean_apply_2(v_inst_4750_, v_head_4755_, v_head_4757_);
                        v___x_4760_ = (crate::leanh::lean_unbox(v___x_4759_) as u8);
                        if v___x_4760_ == 0 {
                            v_x_4752_ = v_tail_4758_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_4756_);
                            crate::leanh::lean_dec_ref_known(v_x_4751_, 2);
                            v_x_4751_ = v_tail_4756_;
                            v_x_4752_ = v_tail_4758_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isSublist___redArg___boxed(
    mut v_inst_4763_: *mut crate::leanh::LeanObject,
    mut v_x_4764_: *mut crate::leanh::LeanObject,
    mut v_x_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4766_: u8 = 0;
    let mut v_r_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ = l_List_isSublist___redArg(v_inst_4763_, v_x_4764_, v_x_4765_);
    v_r_4767_ = crate::leanh::lean_box((v_res_4766_) as usize);
    return v_r_4767_;
}
pub unsafe fn l_List_isSublist(
    mut v_00_u03b1_4768_: *mut crate::leanh::LeanObject,
    mut v_inst_4769_: *mut crate::leanh::LeanObject,
    mut v_x_4770_: *mut crate::leanh::LeanObject,
    mut v_x_4771_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4772_: u8 = 0;
    v___x_4772_ = l_List_isSublist___redArg(v_inst_4769_, v_x_4770_, v_x_4771_);
    return v___x_4772_;
}
pub unsafe fn l_List_isSublist___boxed(
    mut v_00_u03b1_4773_: *mut crate::leanh::LeanObject,
    mut v_inst_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4777_: u8 = 0;
    let mut v_r_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4777_ = l_List_isSublist(v_00_u03b1_4773_, v_inst_4774_, v_x_4775_, v_x_4776_);
    v_r_4778_ = crate::leanh::lean_box((v_res_4777_) as usize);
    return v_r_4778_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0;
    v___x_4797_ = l_String_toRawSubstring_x27(v___x_4796_);
    return v___x_4797_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(
    mut v_x_4809_: *mut crate::leanh::LeanObject,
    mut v_a_4810_: *mut crate::leanh::LeanObject,
    mut v_a_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: u8 = 0;
    v___x_4812_ = l_List_term___x3c_x2b_x3a___00__closed__1;
    crate::leanh::lean_inc(v_x_4809_);
    v___x_4813_ = l_Lean_Syntax_isOfKind(v_x_4809_, v___x_4812_);
    if v___x_4813_ == 0 {
        let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4809_);
        v___x_4814_ = crate::leanh::lean_box(1);
        v___x_4815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4815_, 0, v___x_4814_);
        crate::leanh::lean_ctor_set(v___x_4815_, 1, v_a_4811_);
        return v___x_4815_;
    } else {
        let mut v_quotContext_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: u8 = 0;
        let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4816_ = crate::leanh::lean_ctor_get(v_a_4810_, 1);
        v_currMacroScope_4817_ = crate::leanh::lean_ctor_get(v_a_4810_, 2);
        v_ref_4818_ = crate::leanh::lean_ctor_get(v_a_4810_, 5);
        v___x_4819_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4820_ = l_Lean_Syntax_getArg(v_x_4809_, v___x_4819_);
        v___x_4821_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4822_ = l_Lean_Syntax_getArg(v_x_4809_, v___x_4821_);
        crate::leanh::lean_dec(v_x_4809_);
        v___x_4823_ = 0;
        v___x_4824_ = l_Lean_SourceInfo_fromRef(v_ref_4818_, v___x_4823_);
        v___x_4825_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_4826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
        v___x_4827_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_4817_);
        crate::leanh::lean_inc(v_quotContext_4816_);
        v___x_4828_ =
            l_Lean_addMacroScope(v_quotContext_4816_, v___x_4827_, v_currMacroScope_4817_);
        v___x_4829_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5;
        crate::leanh::lean_inc_n(v___x_4824_, 2);
        v___x_4830_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4830_, 0, v___x_4824_);
        crate::leanh::lean_ctor_set(v___x_4830_, 1, v___x_4826_);
        crate::leanh::lean_ctor_set(v___x_4830_, 2, v___x_4828_);
        crate::leanh::lean_ctor_set(v___x_4830_, 3, v___x_4829_);
        v___x_4831_ = l_List_lex___auto__1___closed__9;
        v___x_4832_ = l_Lean_Syntax_node2(v___x_4824_, v___x_4831_, v___x_4820_, v___x_4822_);
        v___x_4833_ = l_Lean_Syntax_node2(v___x_4824_, v___x_4825_, v___x_4830_, v___x_4832_);
        v___x_4834_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4834_, 0, v___x_4833_);
        crate::leanh::lean_ctor_set(v___x_4834_, 1, v_a_4811_);
        return v___x_4834_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(
    mut v_x_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
    mut v_a_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(
            v_x_4835_, v_a_4836_, v_a_4837_,
        );
    crate::leanh::lean_dec_ref(v_a_4836_);
    return v_res_4838_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(
    mut v_x_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    v___x_4842_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    crate::leanh::lean_inc(v_x_4839_);
    v___x_4843_ = l_Lean_Syntax_isOfKind(v_x_4839_, v___x_4842_);
    if v___x_4843_ == 0 {
        let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4839_);
        v___x_4844_ = crate::leanh::lean_box(0);
        v___x_4845_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4845_, 0, v___x_4844_);
        crate::leanh::lean_ctor_set(v___x_4845_, 1, v_a_4841_);
        return v___x_4845_;
    } else {
        let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: u8 = 0;
        v___x_4846_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4847_ = l_Lean_Syntax_getArg(v_x_4839_, v___x_4846_);
        v___x_4848_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        crate::leanh::lean_inc(v___x_4847_);
        v___x_4849_ = l_Lean_Syntax_isOfKind(v___x_4847_, v___x_4848_);
        if v___x_4849_ == 0 {
            let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4847_);
            crate::leanh::lean_dec(v_x_4839_);
            v___x_4850_ = crate::leanh::lean_box(0);
            v___x_4851_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4851_, 0, v___x_4850_);
            crate::leanh::lean_ctor_set(v___x_4851_, 1, v_a_4841_);
            return v___x_4851_;
        } else {
            let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4855_: u8 = 0;
            v___x_4852_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_4853_ = l_Lean_Syntax_getArg(v_x_4839_, v___x_4852_);
            crate::leanh::lean_dec(v_x_4839_);
            v___x_4854_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_4853_);
            v___x_4855_ = l_Lean_Syntax_matchesNull(v___x_4853_, v___x_4854_);
            if v___x_4855_ == 0 {
                let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4853_);
                crate::leanh::lean_dec(v___x_4847_);
                v___x_4856_ = crate::leanh::lean_box(0);
                v___x_4857_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4857_, 0, v___x_4856_);
                crate::leanh::lean_ctor_set(v___x_4857_, 1, v_a_4841_);
                return v___x_4857_;
            } else {
                let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4861_: u8 = 0;
                let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4858_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4846_);
                v___x_4859_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4852_);
                crate::leanh::lean_dec(v___x_4853_);
                v_ref_4860_ = l_Lean_replaceRef(v___x_4847_, v_a_4840_);
                crate::leanh::lean_dec(v___x_4847_);
                v___x_4861_ = 0;
                v___x_4862_ = l_Lean_SourceInfo_fromRef(v_ref_4860_, v___x_4861_);
                crate::leanh::lean_dec(v_ref_4860_);
                v___x_4863_ = l_List_term___x3c_x2b_x3a___00__closed__1;
                v___x_4864_ = l_List_term___x3c_x2b_x3a___00__closed__2;
                crate::leanh::lean_inc(v___x_4862_);
                v___x_4865_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4865_, 0, v___x_4862_);
                crate::leanh::lean_ctor_set(v___x_4865_, 1, v___x_4864_);
                v___x_4866_ = l_Lean_Syntax_node3(
                    v___x_4862_,
                    v___x_4863_,
                    v___x_4858_,
                    v___x_4865_,
                    v___x_4859_,
                );
                v___x_4867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4866_);
                crate::leanh::lean_ctor_set(v___x_4867_, 1, v_a_4841_);
                return v___x_4867_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(
    mut v_x_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(
        v_x_4868_, v_a_4869_, v_a_4870_,
    );
    crate::leanh::lean_dec(v_a_4869_);
    return v_res_4871_;
}
pub unsafe fn l_List_isPrefixOf___redArg(
    mut v_inst_4872_: *mut crate::leanh::LeanObject,
    mut v_x_4873_: *mut crate::leanh::LeanObject,
    mut v_x_4874_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: u8 = 0;
    let mut v_head_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4873_) == 0 {
                    crate::leanh::lean_dec(v_x_4874_);
                    crate::leanh::lean_dec_ref(v_inst_4872_);
                    v___x_4875_ = 1;
                    return v___x_4875_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4874_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_4873_, 2);
                        crate::leanh::lean_dec_ref(v_inst_4872_);
                        v___x_4876_ = 0;
                        return v___x_4876_;
                    } else {
                        v_head_4877_ = crate::leanh::lean_ctor_get(v_x_4873_, 0);
                        crate::leanh::lean_inc(v_head_4877_);
                        v_tail_4878_ = crate::leanh::lean_ctor_get(v_x_4873_, 1);
                        crate::leanh::lean_inc(v_tail_4878_);
                        crate::leanh::lean_dec_ref_known(v_x_4873_, 2);
                        v_head_4879_ = crate::leanh::lean_ctor_get(v_x_4874_, 0);
                        crate::leanh::lean_inc(v_head_4879_);
                        v_tail_4880_ = crate::leanh::lean_ctor_get(v_x_4874_, 1);
                        crate::leanh::lean_inc(v_tail_4880_);
                        crate::leanh::lean_dec_ref_known(v_x_4874_, 2);
                        crate::leanh::lean_inc_ref(v_inst_4872_);
                        v___x_4881_ =
                            crate::leanh::lean_apply_2(v_inst_4872_, v_head_4877_, v_head_4879_);
                        v___x_4882_ = (crate::leanh::lean_unbox(v___x_4881_) as u8);
                        if v___x_4882_ == 0 {
                            crate::leanh::lean_dec(v_tail_4880_);
                            crate::leanh::lean_dec(v_tail_4878_);
                            crate::leanh::lean_dec_ref(v_inst_4872_);
                            v___x_4883_ = (crate::leanh::lean_unbox(v___x_4881_) as u8);
                            return v___x_4883_;
                        } else {
                            v_x_4873_ = v_tail_4878_;
                            v_x_4874_ = v_tail_4880_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isPrefixOf___redArg___boxed(
    mut v_inst_4885_: *mut crate::leanh::LeanObject,
    mut v_x_4886_: *mut crate::leanh::LeanObject,
    mut v_x_4887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4888_: u8 = 0;
    let mut v_r_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4888_ = l_List_isPrefixOf___redArg(v_inst_4885_, v_x_4886_, v_x_4887_);
    v_r_4889_ = crate::leanh::lean_box((v_res_4888_) as usize);
    return v_r_4889_;
}
pub unsafe fn l_List_isPrefixOf(
    mut v_00_u03b1_4890_: *mut crate::leanh::LeanObject,
    mut v_inst_4891_: *mut crate::leanh::LeanObject,
    mut v_x_4892_: *mut crate::leanh::LeanObject,
    mut v_x_4893_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4894_: u8 = 0;
    v___x_4894_ = l_List_isPrefixOf___redArg(v_inst_4891_, v_x_4892_, v_x_4893_);
    return v___x_4894_;
}
pub unsafe fn l_List_isPrefixOf___boxed(
    mut v_00_u03b1_4895_: *mut crate::leanh::LeanObject,
    mut v_inst_4896_: *mut crate::leanh::LeanObject,
    mut v_x_4897_: *mut crate::leanh::LeanObject,
    mut v_x_4898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4899_: u8 = 0;
    let mut v_r_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4899_ = l_List_isPrefixOf(v_00_u03b1_4895_, v_inst_4896_, v_x_4897_, v_x_4898_);
    v_r_4900_ = crate::leanh::lean_box((v_res_4899_) as usize);
    return v_r_4900_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(
    mut v_x_4901_: *mut crate::leanh::LeanObject,
    mut v_x_4902_: *mut crate::leanh::LeanObject,
    mut v_h__1_4903_: *mut crate::leanh::LeanObject,
    mut v_h__2_4904_: *mut crate::leanh::LeanObject,
    mut v_h__3_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4901_) == 0 {
        let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4905_);
        crate::leanh::lean_dec(v_h__2_4904_);
        v___x_4906_ = crate::leanh::lean_apply_1(v_h__1_4903_, v_x_4902_);
        return v___x_4906_;
    } else {
        crate::leanh::lean_dec(v_h__1_4903_);
        if crate::leanh::lean_obj_tag(v_x_4902_) == 0 {
            let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4905_);
            v___x_4907_ =
                crate::leanh::lean_apply_2(v_h__2_4904_, v_x_4901_, crate::leanh::lean_box(0));
            return v___x_4907_;
        } else {
            let mut v_head_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4904_);
            v_head_4908_ = crate::leanh::lean_ctor_get(v_x_4901_, 0);
            crate::leanh::lean_inc(v_head_4908_);
            v_tail_4909_ = crate::leanh::lean_ctor_get(v_x_4901_, 1);
            crate::leanh::lean_inc(v_tail_4909_);
            crate::leanh::lean_dec_ref_known(v_x_4901_, 2);
            v_head_4910_ = crate::leanh::lean_ctor_get(v_x_4902_, 0);
            crate::leanh::lean_inc(v_head_4910_);
            v_tail_4911_ = crate::leanh::lean_ctor_get(v_x_4902_, 1);
            crate::leanh::lean_inc(v_tail_4911_);
            crate::leanh::lean_dec_ref_known(v_x_4902_, 2);
            v___x_4912_ = crate::leanh::lean_apply_4(
                v_h__3_4905_,
                v_head_4908_,
                v_tail_4909_,
                v_head_4910_,
                v_tail_4911_,
            );
            return v___x_4912_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter(
    mut v_00_u03b1_4913_: *mut crate::leanh::LeanObject,
    mut v_motive_4914_: *mut crate::leanh::LeanObject,
    mut v_x_4915_: *mut crate::leanh::LeanObject,
    mut v_x_4916_: *mut crate::leanh::LeanObject,
    mut v_h__1_4917_: *mut crate::leanh::LeanObject,
    mut v_h__2_4918_: *mut crate::leanh::LeanObject,
    mut v_h__3_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4915_) == 0 {
        let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_4919_);
        crate::leanh::lean_dec(v_h__2_4918_);
        v___x_4920_ = crate::leanh::lean_apply_1(v_h__1_4917_, v_x_4916_);
        return v___x_4920_;
    } else {
        crate::leanh::lean_dec(v_h__1_4917_);
        if crate::leanh::lean_obj_tag(v_x_4916_) == 0 {
            let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_4919_);
            v___x_4921_ =
                crate::leanh::lean_apply_2(v_h__2_4918_, v_x_4915_, crate::leanh::lean_box(0));
            return v___x_4921_;
        } else {
            let mut v_head_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_4918_);
            v_head_4922_ = crate::leanh::lean_ctor_get(v_x_4915_, 0);
            crate::leanh::lean_inc(v_head_4922_);
            v_tail_4923_ = crate::leanh::lean_ctor_get(v_x_4915_, 1);
            crate::leanh::lean_inc(v_tail_4923_);
            crate::leanh::lean_dec_ref_known(v_x_4915_, 2);
            v_head_4924_ = crate::leanh::lean_ctor_get(v_x_4916_, 0);
            crate::leanh::lean_inc(v_head_4924_);
            v_tail_4925_ = crate::leanh::lean_ctor_get(v_x_4916_, 1);
            crate::leanh::lean_inc(v_tail_4925_);
            crate::leanh::lean_dec_ref_known(v_x_4916_, 2);
            v___x_4926_ = crate::leanh::lean_apply_4(
                v_h__3_4919_,
                v_head_4922_,
                v_tail_4923_,
                v_head_4924_,
                v_tail_4925_,
            );
            return v___x_4926_;
        }
    }
}
pub unsafe fn l_List_isPrefixOf_x3f___redArg(
    mut v_inst_4927_: *mut crate::leanh::LeanObject,
    mut v_x_4928_: *mut crate::leanh::LeanObject,
    mut v_x_4929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4928_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_4927_);
                    v___x_4930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4930_, 0, v_x_4929_);
                    return v___x_4930_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4929_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_4928_, 2);
                        crate::leanh::lean_dec_ref(v_inst_4927_);
                        v___x_4931_ = crate::leanh::lean_box(0);
                        return v___x_4931_;
                    } else {
                        v_head_4932_ = crate::leanh::lean_ctor_get(v_x_4928_, 0);
                        crate::leanh::lean_inc(v_head_4932_);
                        v_tail_4933_ = crate::leanh::lean_ctor_get(v_x_4928_, 1);
                        crate::leanh::lean_inc(v_tail_4933_);
                        crate::leanh::lean_dec_ref_known(v_x_4928_, 2);
                        v_head_4934_ = crate::leanh::lean_ctor_get(v_x_4929_, 0);
                        crate::leanh::lean_inc(v_head_4934_);
                        v_tail_4935_ = crate::leanh::lean_ctor_get(v_x_4929_, 1);
                        crate::leanh::lean_inc(v_tail_4935_);
                        crate::leanh::lean_dec_ref_known(v_x_4929_, 2);
                        crate::leanh::lean_inc_ref(v_inst_4927_);
                        v___x_4936_ =
                            crate::leanh::lean_apply_2(v_inst_4927_, v_head_4932_, v_head_4934_);
                        v___x_4937_ = (crate::leanh::lean_unbox(v___x_4936_) as u8);
                        if v___x_4937_ == 0 {
                            crate::leanh::lean_dec(v_tail_4935_);
                            crate::leanh::lean_dec(v_tail_4933_);
                            crate::leanh::lean_dec_ref(v_inst_4927_);
                            v___x_4938_ = crate::leanh::lean_box(0);
                            return v___x_4938_;
                        } else {
                            v_x_4928_ = v_tail_4933_;
                            v_x_4929_ = v_tail_4935_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isPrefixOf_x3f(
    mut v_00_u03b1_4940_: *mut crate::leanh::LeanObject,
    mut v_inst_4941_: *mut crate::leanh::LeanObject,
    mut v_x_4942_: *mut crate::leanh::LeanObject,
    mut v_x_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4944_ = l_List_isPrefixOf_x3f___redArg(v_inst_4941_, v_x_4942_, v_x_4943_);
    return v___x_4944_;
}
pub unsafe fn l_List_isSuffixOf___redArg(
    mut v_inst_4945_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4946_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4947_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: u8 = 0;
    v___x_4948_ = l_List_reverse___redArg(v_l_u2081_4946_);
    v___x_4949_ = l_List_reverse___redArg(v_l_u2082_4947_);
    v___x_4950_ = l_List_isPrefixOf___redArg(v_inst_4945_, v___x_4948_, v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_List_isSuffixOf___redArg___boxed(
    mut v_inst_4951_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4952_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4954_: u8 = 0;
    let mut v_r_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l_List_isSuffixOf___redArg(v_inst_4951_, v_l_u2081_4952_, v_l_u2082_4953_);
    v_r_4955_ = crate::leanh::lean_box((v_res_4954_) as usize);
    return v_r_4955_;
}
pub unsafe fn l_List_isSuffixOf(
    mut v_00_u03b1_4956_: *mut crate::leanh::LeanObject,
    mut v_inst_4957_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4958_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4959_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4960_: u8 = 0;
    v___x_4960_ = l_List_isSuffixOf___redArg(v_inst_4957_, v_l_u2081_4958_, v_l_u2082_4959_);
    return v___x_4960_;
}
pub unsafe fn l_List_isSuffixOf___boxed(
    mut v_00_u03b1_4961_: *mut crate::leanh::LeanObject,
    mut v_inst_4962_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4963_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4965_: u8 = 0;
    let mut v_r_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4965_ = l_List_isSuffixOf(
        v_00_u03b1_4961_,
        v_inst_4962_,
        v_l_u2081_4963_,
        v_l_u2082_4964_,
    );
    v_r_4966_ = crate::leanh::lean_box((v_res_4965_) as usize);
    return v_r_4966_;
}
pub unsafe fn l_List_isSuffixOf_x3f___redArg(
    mut v_inst_4967_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4968_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4970_ = l_List_reverse___redArg(v_l_u2081_4968_);
                v___x_4971_ = l_List_reverse___redArg(v_l_u2082_4969_);
                v___x_4972_ =
                    l_List_isPrefixOf_x3f___redArg(v_inst_4967_, v___x_4970_, v___x_4971_);
                if crate::leanh::lean_obj_tag(v___x_4972_) == 0 {
                    return v___x_4972_;
                } else {
                    v_val_4973_ = crate::leanh::lean_ctor_get(v___x_4972_, 0);
                    v_isSharedCheck_4981_ = (!crate::leanh::lean_is_exclusive(v___x_4972_)) as u8;
                    if v_isSharedCheck_4981_ == 0 {
                        v___x_4975_ = v___x_4972_;
                        v_isShared_4976_ = v_isSharedCheck_4981_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4973_);
                        crate::leanh::lean_dec(v___x_4972_);
                        v___x_4975_ = crate::leanh::lean_box(0);
                        v_isShared_4976_ = v_isSharedCheck_4981_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4977_ = l_List_reverse___redArg(v_val_4973_);
                if v_isShared_4976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4975_, 0, v___x_4977_);
                    v___x_4979_ = v___x_4975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4977_);
                    v___x_4979_ = v_reuseFailAlloc_4980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isSuffixOf_x3f(
    mut v_00_u03b1_4982_: *mut crate::leanh::LeanObject,
    mut v_inst_4983_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_4984_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_4985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l_List_isSuffixOf_x3f___redArg(v_inst_4983_, v_l_u2081_4984_, v_l_u2082_4985_);
    return v___x_4986_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5004_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0;
    v___x_5005_ = l_String_toRawSubstring_x27(v___x_5004_);
    return v___x_5005_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(
    mut v_x_5017_: *mut crate::leanh::LeanObject,
    mut v_a_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u8 = 0;
    v___x_5020_ = l_List_term___x3c_x3a_x2b___00__closed__1;
    crate::leanh::lean_inc(v_x_5017_);
    v___x_5021_ = l_Lean_Syntax_isOfKind(v_x_5017_, v___x_5020_);
    if v___x_5021_ == 0 {
        let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5017_);
        v___x_5022_ = crate::leanh::lean_box(1);
        v___x_5023_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5023_, 0, v___x_5022_);
        crate::leanh::lean_ctor_set(v___x_5023_, 1, v_a_5019_);
        return v___x_5023_;
    } else {
        let mut v_quotContext_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5031_: u8 = 0;
        let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5024_ = crate::leanh::lean_ctor_get(v_a_5018_, 1);
        v_currMacroScope_5025_ = crate::leanh::lean_ctor_get(v_a_5018_, 2);
        v_ref_5026_ = crate::leanh::lean_ctor_get(v_a_5018_, 5);
        v___x_5027_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5028_ = l_Lean_Syntax_getArg(v_x_5017_, v___x_5027_);
        v___x_5029_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_5030_ = l_Lean_Syntax_getArg(v_x_5017_, v___x_5029_);
        crate::leanh::lean_dec(v_x_5017_);
        v___x_5031_ = 0;
        v___x_5032_ = l_Lean_SourceInfo_fromRef(v_ref_5026_, v___x_5031_);
        v___x_5033_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5034_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
        v___x_5035_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_5025_);
        crate::leanh::lean_inc(v_quotContext_5024_);
        v___x_5036_ =
            l_Lean_addMacroScope(v_quotContext_5024_, v___x_5035_, v_currMacroScope_5025_);
        v___x_5037_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5;
        crate::leanh::lean_inc_n(v___x_5032_, 2);
        v___x_5038_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5038_, 0, v___x_5032_);
        crate::leanh::lean_ctor_set(v___x_5038_, 1, v___x_5034_);
        crate::leanh::lean_ctor_set(v___x_5038_, 2, v___x_5036_);
        crate::leanh::lean_ctor_set(v___x_5038_, 3, v___x_5037_);
        v___x_5039_ = l_List_lex___auto__1___closed__9;
        v___x_5040_ = l_Lean_Syntax_node2(v___x_5032_, v___x_5039_, v___x_5028_, v___x_5030_);
        v___x_5041_ = l_Lean_Syntax_node2(v___x_5032_, v___x_5033_, v___x_5038_, v___x_5040_);
        v___x_5042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5042_, 0, v___x_5041_);
        crate::leanh::lean_ctor_set(v___x_5042_, 1, v_a_5019_);
        return v___x_5042_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(
    mut v_x_5043_: *mut crate::leanh::LeanObject,
    mut v_a_5044_: *mut crate::leanh::LeanObject,
    mut v_a_5045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5046_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(
            v_x_5043_, v_a_5044_, v_a_5045_,
        );
    crate::leanh::lean_dec_ref(v_a_5044_);
    return v_res_5046_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(
    mut v_x_5047_: *mut crate::leanh::LeanObject,
    mut v_a_5048_: *mut crate::leanh::LeanObject,
    mut v_a_5049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    v___x_5050_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    crate::leanh::lean_inc(v_x_5047_);
    v___x_5051_ = l_Lean_Syntax_isOfKind(v_x_5047_, v___x_5050_);
    if v___x_5051_ == 0 {
        let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5047_);
        v___x_5052_ = crate::leanh::lean_box(0);
        v___x_5053_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5053_, 0, v___x_5052_);
        crate::leanh::lean_ctor_set(v___x_5053_, 1, v_a_5049_);
        return v___x_5053_;
    } else {
        let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5057_: u8 = 0;
        v___x_5054_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5055_ = l_Lean_Syntax_getArg(v_x_5047_, v___x_5054_);
        v___x_5056_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        crate::leanh::lean_inc(v___x_5055_);
        v___x_5057_ = l_Lean_Syntax_isOfKind(v___x_5055_, v___x_5056_);
        if v___x_5057_ == 0 {
            let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5055_);
            crate::leanh::lean_dec(v_x_5047_);
            v___x_5058_ = crate::leanh::lean_box(0);
            v___x_5059_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5059_, 0, v___x_5058_);
            crate::leanh::lean_ctor_set(v___x_5059_, 1, v_a_5049_);
            return v___x_5059_;
        } else {
            let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5063_: u8 = 0;
            v___x_5060_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_5061_ = l_Lean_Syntax_getArg(v_x_5047_, v___x_5060_);
            crate::leanh::lean_dec(v_x_5047_);
            v___x_5062_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_5061_);
            v___x_5063_ = l_Lean_Syntax_matchesNull(v___x_5061_, v___x_5062_);
            if v___x_5063_ == 0 {
                let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_5061_);
                crate::leanh::lean_dec(v___x_5055_);
                v___x_5064_ = crate::leanh::lean_box(0);
                v___x_5065_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5065_, 0, v___x_5064_);
                crate::leanh::lean_ctor_set(v___x_5065_, 1, v_a_5049_);
                return v___x_5065_;
            } else {
                let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5069_: u8 = 0;
                let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5066_ = l_Lean_Syntax_getArg(v___x_5061_, v___x_5054_);
                v___x_5067_ = l_Lean_Syntax_getArg(v___x_5061_, v___x_5060_);
                crate::leanh::lean_dec(v___x_5061_);
                v_ref_5068_ = l_Lean_replaceRef(v___x_5055_, v_a_5048_);
                crate::leanh::lean_dec(v___x_5055_);
                v___x_5069_ = 0;
                v___x_5070_ = l_Lean_SourceInfo_fromRef(v_ref_5068_, v___x_5069_);
                crate::leanh::lean_dec(v_ref_5068_);
                v___x_5071_ = l_List_term___x3c_x3a_x2b___00__closed__1;
                v___x_5072_ = l_List_term___x3c_x3a_x2b___00__closed__2;
                crate::leanh::lean_inc(v___x_5070_);
                v___x_5073_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5073_, 0, v___x_5070_);
                crate::leanh::lean_ctor_set(v___x_5073_, 1, v___x_5072_);
                v___x_5074_ = l_Lean_Syntax_node3(
                    v___x_5070_,
                    v___x_5071_,
                    v___x_5066_,
                    v___x_5073_,
                    v___x_5067_,
                );
                v___x_5075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5075_, 0, v___x_5074_);
                crate::leanh::lean_ctor_set(v___x_5075_, 1, v_a_5049_);
                return v___x_5075_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(
    mut v_x_5076_: *mut crate::leanh::LeanObject,
    mut v_a_5077_: *mut crate::leanh::LeanObject,
    mut v_a_5078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(
        v_x_5076_, v_a_5077_, v_a_5078_,
    );
    crate::leanh::lean_dec(v_a_5077_);
    return v_res_5079_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5097_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0;
    v___x_5098_ = l_String_toRawSubstring_x27(v___x_5097_);
    return v___x_5098_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(
    mut v_x_5110_: *mut crate::leanh::LeanObject,
    mut v_a_5111_: *mut crate::leanh::LeanObject,
    mut v_a_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    v___x_5113_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__1;
    crate::leanh::lean_inc(v_x_5110_);
    v___x_5114_ = l_Lean_Syntax_isOfKind(v_x_5110_, v___x_5113_);
    if v___x_5114_ == 0 {
        let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5110_);
        v___x_5115_ = crate::leanh::lean_box(1);
        v___x_5116_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5115_);
        crate::leanh::lean_ctor_set(v___x_5116_, 1, v_a_5112_);
        return v___x_5116_;
    } else {
        let mut v_quotContext_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5124_: u8 = 0;
        let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5117_ = crate::leanh::lean_ctor_get(v_a_5111_, 1);
        v_currMacroScope_5118_ = crate::leanh::lean_ctor_get(v_a_5111_, 2);
        v_ref_5119_ = crate::leanh::lean_ctor_get(v_a_5111_, 5);
        v___x_5120_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5121_ = l_Lean_Syntax_getArg(v_x_5110_, v___x_5120_);
        v___x_5122_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_5123_ = l_Lean_Syntax_getArg(v_x_5110_, v___x_5122_);
        crate::leanh::lean_dec(v_x_5110_);
        v___x_5124_ = 0;
        v___x_5125_ = l_Lean_SourceInfo_fromRef(v_ref_5119_, v___x_5124_);
        v___x_5126_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5127_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
        v___x_5128_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_5118_);
        crate::leanh::lean_inc(v_quotContext_5117_);
        v___x_5129_ =
            l_Lean_addMacroScope(v_quotContext_5117_, v___x_5128_, v_currMacroScope_5118_);
        v___x_5130_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5;
        crate::leanh::lean_inc_n(v___x_5125_, 2);
        v___x_5131_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5131_, 0, v___x_5125_);
        crate::leanh::lean_ctor_set(v___x_5131_, 1, v___x_5127_);
        crate::leanh::lean_ctor_set(v___x_5131_, 2, v___x_5129_);
        crate::leanh::lean_ctor_set(v___x_5131_, 3, v___x_5130_);
        v___x_5132_ = l_List_lex___auto__1___closed__9;
        v___x_5133_ = l_Lean_Syntax_node2(v___x_5125_, v___x_5132_, v___x_5121_, v___x_5123_);
        v___x_5134_ = l_Lean_Syntax_node2(v___x_5125_, v___x_5126_, v___x_5131_, v___x_5133_);
        v___x_5135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5134_);
        crate::leanh::lean_ctor_set(v___x_5135_, 1, v_a_5112_);
        return v___x_5135_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(
    mut v_x_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
    mut v_a_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5139_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(
            v_x_5136_, v_a_5137_, v_a_5138_,
        );
    crate::leanh::lean_dec_ref(v_a_5137_);
    return v_res_5139_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(
    mut v_x_5140_: *mut crate::leanh::LeanObject,
    mut v_a_5141_: *mut crate::leanh::LeanObject,
    mut v_a_5142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: u8 = 0;
    v___x_5143_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    crate::leanh::lean_inc(v_x_5140_);
    v___x_5144_ = l_Lean_Syntax_isOfKind(v_x_5140_, v___x_5143_);
    if v___x_5144_ == 0 {
        let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5140_);
        v___x_5145_ = crate::leanh::lean_box(0);
        v___x_5146_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
        crate::leanh::lean_ctor_set(v___x_5146_, 1, v_a_5142_);
        return v___x_5146_;
    } else {
        let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5150_: u8 = 0;
        v___x_5147_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5148_ = l_Lean_Syntax_getArg(v_x_5140_, v___x_5147_);
        v___x_5149_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        crate::leanh::lean_inc(v___x_5148_);
        v___x_5150_ = l_Lean_Syntax_isOfKind(v___x_5148_, v___x_5149_);
        if v___x_5150_ == 0 {
            let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5148_);
            crate::leanh::lean_dec(v_x_5140_);
            v___x_5151_ = crate::leanh::lean_box(0);
            v___x_5152_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
            crate::leanh::lean_ctor_set(v___x_5152_, 1, v_a_5142_);
            return v___x_5152_;
        } else {
            let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5156_: u8 = 0;
            v___x_5153_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_5154_ = l_Lean_Syntax_getArg(v_x_5140_, v___x_5153_);
            crate::leanh::lean_dec(v_x_5140_);
            v___x_5155_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_5154_);
            v___x_5156_ = l_Lean_Syntax_matchesNull(v___x_5154_, v___x_5155_);
            if v___x_5156_ == 0 {
                let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_5154_);
                crate::leanh::lean_dec(v___x_5148_);
                v___x_5157_ = crate::leanh::lean_box(0);
                v___x_5158_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5158_, 0, v___x_5157_);
                crate::leanh::lean_ctor_set(v___x_5158_, 1, v_a_5142_);
                return v___x_5158_;
            } else {
                let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5162_: u8 = 0;
                let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5159_ = l_Lean_Syntax_getArg(v___x_5154_, v___x_5147_);
                v___x_5160_ = l_Lean_Syntax_getArg(v___x_5154_, v___x_5153_);
                crate::leanh::lean_dec(v___x_5154_);
                v_ref_5161_ = l_Lean_replaceRef(v___x_5148_, v_a_5141_);
                crate::leanh::lean_dec(v___x_5148_);
                v___x_5162_ = 0;
                v___x_5163_ = l_Lean_SourceInfo_fromRef(v_ref_5161_, v___x_5162_);
                crate::leanh::lean_dec(v_ref_5161_);
                v___x_5164_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__1;
                v___x_5165_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__2;
                crate::leanh::lean_inc(v___x_5163_);
                v___x_5166_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5166_, 0, v___x_5163_);
                crate::leanh::lean_ctor_set(v___x_5166_, 1, v___x_5165_);
                v___x_5167_ = l_Lean_Syntax_node3(
                    v___x_5163_,
                    v___x_5164_,
                    v___x_5159_,
                    v___x_5166_,
                    v___x_5160_,
                );
                v___x_5168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5168_, 0, v___x_5167_);
                crate::leanh::lean_ctor_set(v___x_5168_, 1, v_a_5142_);
                return v___x_5168_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(
    mut v_x_5169_: *mut crate::leanh::LeanObject,
    mut v_a_5170_: *mut crate::leanh::LeanObject,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5172_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(
        v_x_5169_, v_a_5170_, v_a_5171_,
    );
    crate::leanh::lean_dec(v_a_5170_);
    return v_res_5172_;
}
pub unsafe fn l_List_isInfixOf__internal___redArg(
    mut v_inst_5173_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_5174_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_5175_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5176_: u8 = 0;
    let mut v_tail_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_l_u2082_5175_);
                crate::leanh::lean_inc(v_l_u2081_5174_);
                crate::leanh::lean_inc_ref(v_inst_5173_);
                v___x_5176_ =
                    l_List_isPrefixOf___redArg(v_inst_5173_, v_l_u2081_5174_, v_l_u2082_5175_);
                if v___x_5176_ == 0 {
                    if crate::leanh::lean_obj_tag(v_l_u2082_5175_) == 0 {
                        crate::leanh::lean_dec(v_l_u2081_5174_);
                        crate::leanh::lean_dec_ref(v_inst_5173_);
                        return v___x_5176_;
                    } else {
                        v_tail_5177_ = crate::leanh::lean_ctor_get(v_l_u2082_5175_, 1);
                        crate::leanh::lean_inc(v_tail_5177_);
                        crate::leanh::lean_dec_ref_known(v_l_u2082_5175_, 2);
                        v_l_u2082_5175_ = v_tail_5177_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_l_u2082_5175_);
                    crate::leanh::lean_dec(v_l_u2081_5174_);
                    crate::leanh::lean_dec_ref(v_inst_5173_);
                    return v___x_5176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isInfixOf__internal___redArg___boxed(
    mut v_inst_5179_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_5180_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5182_: u8 = 0;
    let mut v_r_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5182_ =
        l_List_isInfixOf__internal___redArg(v_inst_5179_, v_l_u2081_5180_, v_l_u2082_5181_);
    v_r_5183_ = crate::leanh::lean_box((v_res_5182_) as usize);
    return v_r_5183_;
}
pub unsafe fn l_List_isInfixOf__internal(
    mut v_00_u03b1_5184_: *mut crate::leanh::LeanObject,
    mut v_inst_5185_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_5186_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_5187_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5188_: u8 = 0;
    v___x_5188_ =
        l_List_isInfixOf__internal___redArg(v_inst_5185_, v_l_u2081_5186_, v_l_u2082_5187_);
    return v___x_5188_;
}
pub unsafe fn l_List_isInfixOf__internal___boxed(
    mut v_00_u03b1_5189_: *mut crate::leanh::LeanObject,
    mut v_inst_5190_: *mut crate::leanh::LeanObject,
    mut v_l_u2081_5191_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_5192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5193_: u8 = 0;
    let mut v_r_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_List_isInfixOf__internal(
        v_00_u03b1_5189_,
        v_inst_5190_,
        v_l_u2081_5191_,
        v_l_u2082_5192_,
    );
    v_r_5194_ = crate::leanh::lean_box((v_res_5193_) as usize);
    return v_r_5194_;
}
pub unsafe fn l_List_splitAt_go___redArg(
    mut v_l_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
    mut v_a_5198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5203_: u8 = 0;
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v_one_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_unused_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5196_) == 0 {
                    crate::leanh::lean_dec(v_a_5198_);
                    crate::leanh::lean_dec(v_a_5197_);
                    v___x_5199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5199_, 0, v_l_5195_);
                    crate::leanh::lean_ctor_set(v___x_5199_, 1, v_a_5196_);
                    return v___x_5199_;
                } else {
                    v_head_5200_ = crate::leanh::lean_ctor_get(v_a_5196_, 0);
                    v_tail_5201_ = crate::leanh::lean_ctor_get(v_a_5196_, 1);
                    v_zero_5202_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_5203_ = lean_nat_dec_eq(v_a_5197_, v_zero_5202_);
                    if v_isZero_5203_ == 1 {
                        crate::leanh::lean_dec(v_a_5197_);
                        crate::leanh::lean_dec(v_l_5195_);
                        v___x_5204_ = l_List_reverse___redArg(v_a_5198_);
                        v___x_5205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5205_, 0, v___x_5204_);
                        crate::leanh::lean_ctor_set(v___x_5205_, 1, v_a_5196_);
                        return v___x_5205_;
                    } else {
                        crate::leanh::lean_inc(v_tail_5201_);
                        crate::leanh::lean_inc(v_head_5200_);
                        v_isSharedCheck_5215_ = (!crate::leanh::lean_is_exclusive(v_a_5196_)) as u8;
                        if v_isSharedCheck_5215_ == 0 {
                            v_unused_5216_ = crate::leanh::lean_ctor_get(v_a_5196_, 1);
                            crate::leanh::lean_dec(v_unused_5216_);
                            v_unused_5217_ = crate::leanh::lean_ctor_get(v_a_5196_, 0);
                            crate::leanh::lean_dec(v_unused_5217_);
                            v___x_5207_ = v_a_5196_;
                            v_isShared_5208_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_5196_);
                            v___x_5207_ = crate::leanh::lean_box(0);
                            v_isShared_5208_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5209_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_5210_ = lean_nat_sub(v_a_5197_, v_one_5209_);
                crate::leanh::lean_dec(v_a_5197_);
                if v_isShared_5208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5207_, 1, v_a_5198_);
                    v___x_5212_ = v___x_5207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_head_5200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 1, v_a_5198_);
                    v___x_5212_ = v_reuseFailAlloc_5214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5196_ = v_tail_5201_;
                v_a_5197_ = v_n_5210_;
                v_a_5198_ = v___x_5212_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_splitAt_go(
    mut v_00_u03b1_5218_: *mut crate::leanh::LeanObject,
    mut v_l_5219_: *mut crate::leanh::LeanObject,
    mut v_a_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = l_List_splitAt_go___redArg(v_l_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
    return v___x_5223_;
}
pub unsafe fn l_List_splitAt___redArg(
    mut v_n_5224_: *mut crate::leanh::LeanObject,
    mut v_l_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_l_5225_);
    v___x_5227_ = l_List_splitAt_go___redArg(v_l_5225_, v_l_5225_, v_n_5224_, v___x_5226_);
    return v___x_5227_;
}
pub unsafe fn l_List_splitAt(
    mut v_00_u03b1_5228_: *mut crate::leanh::LeanObject,
    mut v_n_5229_: *mut crate::leanh::LeanObject,
    mut v_l_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5231_ = l_List_splitAt___redArg(v_n_5229_, v_l_5230_);
    return v___x_5231_;
}
pub unsafe fn l_List_rotateLeft___redArg(
    mut v_xs_5232_: *mut crate::leanh::LeanObject,
    mut v_i_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_len_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    v_len_5234_ = l_List_length___redArg(v_xs_5232_);
    v___x_5235_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5236_ = lean_nat_dec_le(v_len_5234_, v___x_5235_);
    if v___x_5236_ == 0 {
        let mut v_i_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ys_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zs_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_5237_ = lean_nat_mod(v_i_5233_, v_len_5234_);
        crate::leanh::lean_dec(v_len_5234_);
        crate::leanh::lean_inc(v_xs_5232_);
        v_ys_5238_ = l_List_take___redArg(v_i_5237_, v_xs_5232_);
        v_zs_5239_ = l_List_drop___redArg(v_i_5237_, v_xs_5232_);
        crate::leanh::lean_dec(v_xs_5232_);
        v___x_5240_ = l_List_appendTR___redArg(v_zs_5239_, v_ys_5238_);
        return v___x_5240_;
    } else {
        crate::leanh::lean_dec(v_len_5234_);
        return v_xs_5232_;
    }
}
pub unsafe fn l_List_rotateLeft___redArg___boxed(
    mut v_xs_5241_: *mut crate::leanh::LeanObject,
    mut v_i_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5243_ = l_List_rotateLeft___redArg(v_xs_5241_, v_i_5242_);
    crate::leanh::lean_dec(v_i_5242_);
    return v_res_5243_;
}
pub unsafe fn l_List_rotateLeft(
    mut v_00_u03b1_5244_: *mut crate::leanh::LeanObject,
    mut v_xs_5245_: *mut crate::leanh::LeanObject,
    mut v_i_5246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5247_ = l_List_rotateLeft___redArg(v_xs_5245_, v_i_5246_);
    return v___x_5247_;
}
pub unsafe fn l_List_rotateLeft___boxed(
    mut v_00_u03b1_5248_: *mut crate::leanh::LeanObject,
    mut v_xs_5249_: *mut crate::leanh::LeanObject,
    mut v_i_5250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5251_ = l_List_rotateLeft(v_00_u03b1_5248_, v_xs_5249_, v_i_5250_);
    crate::leanh::lean_dec(v_i_5250_);
    return v_res_5251_;
}
pub unsafe fn l_List_rotateRight___redArg(
    mut v_xs_5252_: *mut crate::leanh::LeanObject,
    mut v_i_5253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_len_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: u8 = 0;
    v_len_5254_ = l_List_length___redArg(v_xs_5252_);
    v___x_5255_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5256_ = lean_nat_dec_le(v_len_5254_, v___x_5255_);
    if v___x_5256_ == 0 {
        let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_i_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ys_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_zs_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5257_ = lean_nat_mod(v_i_5253_, v_len_5254_);
        v_i_5258_ = lean_nat_sub(v_len_5254_, v___x_5257_);
        crate::leanh::lean_dec(v___x_5257_);
        crate::leanh::lean_dec(v_len_5254_);
        crate::leanh::lean_inc(v_xs_5252_);
        v_ys_5259_ = l_List_take___redArg(v_i_5258_, v_xs_5252_);
        v_zs_5260_ = l_List_drop___redArg(v_i_5258_, v_xs_5252_);
        crate::leanh::lean_dec(v_xs_5252_);
        v___x_5261_ = l_List_appendTR___redArg(v_zs_5260_, v_ys_5259_);
        return v___x_5261_;
    } else {
        crate::leanh::lean_dec(v_len_5254_);
        return v_xs_5252_;
    }
}
pub unsafe fn l_List_rotateRight___redArg___boxed(
    mut v_xs_5262_: *mut crate::leanh::LeanObject,
    mut v_i_5263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5264_ = l_List_rotateRight___redArg(v_xs_5262_, v_i_5263_);
    crate::leanh::lean_dec(v_i_5263_);
    return v_res_5264_;
}
pub unsafe fn l_List_rotateRight(
    mut v_00_u03b1_5265_: *mut crate::leanh::LeanObject,
    mut v_xs_5266_: *mut crate::leanh::LeanObject,
    mut v_i_5267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5268_ = l_List_rotateRight___redArg(v_xs_5266_, v_i_5267_);
    return v___x_5268_;
}
pub unsafe fn l_List_rotateRight___boxed(
    mut v_00_u03b1_5269_: *mut crate::leanh::LeanObject,
    mut v_xs_5270_: *mut crate::leanh::LeanObject,
    mut v_i_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l_List_rotateRight(v_00_u03b1_5269_, v_xs_5270_, v_i_5271_);
    crate::leanh::lean_dec(v_i_5271_);
    return v_res_5272_;
}
pub unsafe fn l_List_instDecidablePairwise___redArg(
    mut v_inst_5273_: *mut crate::leanh::LeanObject,
    mut v_x_5274_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5274_) == 0 {
        let mut v___x_5275_: u8 = 0;
        crate::leanh::lean_dec_ref(v_inst_5273_);
        v___x_5275_ = 1;
        return v___x_5275_;
    } else {
        let mut v_head_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: u8 = 0;
        v_head_5276_ = crate::leanh::lean_ctor_get(v_x_5274_, 0);
        crate::leanh::lean_inc(v_head_5276_);
        v_tail_5277_ = crate::leanh::lean_ctor_get(v_x_5274_, 1);
        crate::leanh::lean_inc_n(v_tail_5277_, 2);
        crate::leanh::lean_dec_ref_known(v_x_5274_, 2);
        crate::leanh::lean_inc_ref(v_inst_5273_);
        v___x_5278_ = l_List_instDecidablePairwise___redArg(v_inst_5273_, v_tail_5277_);
        if v___x_5278_ == 0 {
            crate::leanh::lean_dec(v_tail_5277_);
            crate::leanh::lean_dec(v_head_5276_);
            crate::leanh::lean_dec_ref(v_inst_5273_);
            return v___x_5278_;
        } else {
            let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5280_: u8 = 0;
            v___x_5279_ = crate::leanh::lean_apply_1(v_inst_5273_, v_head_5276_);
            v___x_5280_ = l_List_decidableBAll___redArg(v___x_5279_, v_tail_5277_);
            return v___x_5280_;
        }
    }
}
pub unsafe fn l_List_instDecidablePairwise___redArg___boxed(
    mut v_inst_5281_: *mut crate::leanh::LeanObject,
    mut v_x_5282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5283_: u8 = 0;
    let mut v_r_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_List_instDecidablePairwise___redArg(v_inst_5281_, v_x_5282_);
    v_r_5284_ = crate::leanh::lean_box((v_res_5283_) as usize);
    return v_r_5284_;
}
pub unsafe fn l_List_instDecidablePairwise(
    mut v_00_u03b1_5285_: *mut crate::leanh::LeanObject,
    mut v_R_5286_: *mut crate::leanh::LeanObject,
    mut v_inst_5287_: *mut crate::leanh::LeanObject,
    mut v_x_5288_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5289_: u8 = 0;
    v___x_5289_ = l_List_instDecidablePairwise___redArg(v_inst_5287_, v_x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_List_instDecidablePairwise___boxed(
    mut v_00_u03b1_5290_: *mut crate::leanh::LeanObject,
    mut v_R_5291_: *mut crate::leanh::LeanObject,
    mut v_inst_5292_: *mut crate::leanh::LeanObject,
    mut v_x_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5294_: u8 = 0;
    let mut v_r_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ =
        l_List_instDecidablePairwise(v_00_u03b1_5290_, v_R_5291_, v_inst_5292_, v_x_5293_);
    v_r_5295_ = crate::leanh::lean_box((v_res_5294_) as usize);
    return v_r_5295_;
}
pub unsafe fn l_List_nodupDecidable___redArg___lam__0(
    mut v_inst_5296_: *mut crate::leanh::LeanObject,
    mut v_a_5297_: *mut crate::leanh::LeanObject,
    mut v_b_5298_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: u8 = 0;
    v___x_5299_ = crate::leanh::lean_apply_2(v_inst_5296_, v_a_5297_, v_b_5298_);
    v___x_5300_ = (crate::leanh::lean_unbox(v___x_5299_) as u8);
    if v___x_5300_ == 0 {
        let mut v___x_5301_: u8 = 0;
        v___x_5301_ = 1;
        return v___x_5301_;
    } else {
        let mut v___x_5302_: u8 = 0;
        v___x_5302_ = 0;
        return v___x_5302_;
    }
}
pub unsafe fn l_List_nodupDecidable___redArg___lam__0___boxed(
    mut v_inst_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
    mut v_b_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5306_: u8 = 0;
    let mut v_r_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l_List_nodupDecidable___redArg___lam__0(v_inst_5303_, v_a_5304_, v_b_5305_);
    v_r_5307_ = crate::leanh::lean_box((v_res_5306_) as usize);
    return v_r_5307_;
}
pub unsafe fn l_List_nodupDecidable___redArg(
    mut v_inst_5308_: *mut crate::leanh::LeanObject,
    mut v_l_5309_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: u8 = 0;
    v___f_5310_ = crate::leanh::lean_alloc_closure(
        l_List_nodupDecidable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5310_, 0, v_inst_5308_);
    v___x_5311_ = l_List_instDecidablePairwise___redArg(v___f_5310_, v_l_5309_);
    return v___x_5311_;
}
pub unsafe fn l_List_nodupDecidable___redArg___boxed(
    mut v_inst_5312_: *mut crate::leanh::LeanObject,
    mut v_l_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5314_: u8 = 0;
    let mut v_r_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_List_nodupDecidable___redArg(v_inst_5312_, v_l_5313_);
    v_r_5315_ = crate::leanh::lean_box((v_res_5314_) as usize);
    return v_r_5315_;
}
pub unsafe fn l_List_nodupDecidable(
    mut v_00_u03b1_5316_: *mut crate::leanh::LeanObject,
    mut v_inst_5317_: *mut crate::leanh::LeanObject,
    mut v_l_5318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5319_: u8 = 0;
    v___x_5319_ = l_List_nodupDecidable___redArg(v_inst_5317_, v_l_5318_);
    return v___x_5319_;
}
pub unsafe fn l_List_nodupDecidable___boxed(
    mut v_00_u03b1_5320_: *mut crate::leanh::LeanObject,
    mut v_inst_5321_: *mut crate::leanh::LeanObject,
    mut v_l_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5323_: u8 = 0;
    let mut v_r_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5323_ = l_List_nodupDecidable(v_00_u03b1_5320_, v_inst_5321_, v_l_5322_);
    v_r_5324_ = crate::leanh::lean_box((v_res_5323_) as usize);
    return v_r_5324_;
}
pub unsafe fn l_List_replace___redArg(
    mut v_inst_5325_: *mut crate::leanh::LeanObject,
    mut v_x_5326_: *mut crate::leanh::LeanObject,
    mut v_x_5327_: *mut crate::leanh::LeanObject,
    mut v_x_5328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5326_) == 0 {
                    crate::leanh::lean_dec(v_x_5328_);
                    crate::leanh::lean_dec(v_x_5327_);
                    crate::leanh::lean_dec_ref(v_inst_5325_);
                    return v_x_5326_;
                } else {
                    v_head_5329_ = crate::leanh::lean_ctor_get(v_x_5326_, 0);
                    v_tail_5330_ = crate::leanh::lean_ctor_get(v_x_5326_, 1);
                    v_isSharedCheck_5343_ = (!crate::leanh::lean_is_exclusive(v_x_5326_)) as u8;
                    if v_isSharedCheck_5343_ == 0 {
                        v___x_5332_ = v_x_5326_;
                        v_isShared_5333_ = v_isSharedCheck_5343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5330_);
                        crate::leanh::lean_inc(v_head_5329_);
                        crate::leanh::lean_dec(v_x_5326_);
                        v___x_5332_ = crate::leanh::lean_box(0);
                        v_isShared_5333_ = v_isSharedCheck_5343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_5325_);
                crate::leanh::lean_inc(v_head_5329_);
                crate::leanh::lean_inc(v_x_5327_);
                v___x_5334_ = crate::leanh::lean_apply_2(v_inst_5325_, v_x_5327_, v_head_5329_);
                v___x_5335_ = (crate::leanh::lean_unbox(v___x_5334_) as u8);
                if v___x_5335_ == 0 {
                    v___x_5336_ =
                        l_List_replace___redArg(v_inst_5325_, v_tail_5330_, v_x_5327_, v_x_5328_);
                    if v_isShared_5333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5332_, 1, v___x_5336_);
                        v___x_5338_ = v___x_5332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5339_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_head_5329_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5336_);
                        v___x_5338_ = v_reuseFailAlloc_5339_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_head_5329_);
                    crate::leanh::lean_dec(v_x_5327_);
                    crate::leanh::lean_dec_ref(v_inst_5325_);
                    if v_isShared_5333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5332_, 0, v_x_5328_);
                        v___x_5341_ = v___x_5332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5342_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_x_5328_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_tail_5330_);
                        v___x_5341_ = v_reuseFailAlloc_5342_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5338_;
            }
            3 => {
                return v___x_5341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_replace(
    mut v_00_u03b1_5344_: *mut crate::leanh::LeanObject,
    mut v_inst_5345_: *mut crate::leanh::LeanObject,
    mut v_x_5346_: *mut crate::leanh::LeanObject,
    mut v_x_5347_: *mut crate::leanh::LeanObject,
    mut v_x_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5349_ = l_List_replace___redArg(v_inst_5345_, v_x_5346_, v_x_5347_, v_x_5348_);
    return v___x_5349_;
}
pub unsafe fn l_List_modifyTailIdx_go___redArg(
    mut v_f_5350_: *mut crate::leanh::LeanObject,
    mut v_a_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5354_: u8 = 0;
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v_one_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5353_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5354_ = lean_nat_dec_eq(v_a_5351_, v_zero_5353_);
                if v_isZero_5354_ == 1 {
                    v___x_5355_ = crate::leanh::lean_apply_1(v_f_5350_, v_a_5352_);
                    return v___x_5355_;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_5352_) == 0 {
                        crate::leanh::lean_dec_ref(v_f_5350_);
                        return v_a_5352_;
                    } else {
                        v_head_5356_ = crate::leanh::lean_ctor_get(v_a_5352_, 0);
                        v_tail_5357_ = crate::leanh::lean_ctor_get(v_a_5352_, 1);
                        v_isSharedCheck_5367_ = (!crate::leanh::lean_is_exclusive(v_a_5352_)) as u8;
                        if v_isSharedCheck_5367_ == 0 {
                            v___x_5359_ = v_a_5352_;
                            v_isShared_5360_ = v_isSharedCheck_5367_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_5357_);
                            crate::leanh::lean_inc(v_head_5356_);
                            crate::leanh::lean_dec(v_a_5352_);
                            v___x_5359_ = crate::leanh::lean_box(0);
                            v_isShared_5360_ = v_isSharedCheck_5367_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5361_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_5362_ = lean_nat_sub(v_a_5351_, v_one_5361_);
                v___x_5363_ = l_List_modifyTailIdx_go___redArg(v_f_5350_, v_n_5362_, v_tail_5357_);
                crate::leanh::lean_dec(v_n_5362_);
                if v_isShared_5360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5359_, 1, v___x_5363_);
                    v___x_5365_ = v___x_5359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_head_5356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___x_5363_);
                    v___x_5365_ = v_reuseFailAlloc_5366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_modifyTailIdx_go___redArg___boxed(
    mut v_f_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
    mut v_a_5370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_List_modifyTailIdx_go___redArg(v_f_5368_, v_a_5369_, v_a_5370_);
    crate::leanh::lean_dec(v_a_5369_);
    return v_res_5371_;
}
pub unsafe fn l_List_modifyTailIdx_go(
    mut v_00_u03b1_5372_: *mut crate::leanh::LeanObject,
    mut v_f_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = l_List_modifyTailIdx_go___redArg(v_f_5373_, v_a_5374_, v_a_5375_);
    return v___x_5376_;
}
pub unsafe fn l_List_modifyTailIdx_go___boxed(
    mut v_00_u03b1_5377_: *mut crate::leanh::LeanObject,
    mut v_f_5378_: *mut crate::leanh::LeanObject,
    mut v_a_5379_: *mut crate::leanh::LeanObject,
    mut v_a_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l_List_modifyTailIdx_go(v_00_u03b1_5377_, v_f_5378_, v_a_5379_, v_a_5380_);
    crate::leanh::lean_dec(v_a_5379_);
    return v_res_5381_;
}
pub unsafe fn l_List_modifyTailIdx___redArg(
    mut v_l_5382_: *mut crate::leanh::LeanObject,
    mut v_i_5383_: *mut crate::leanh::LeanObject,
    mut v_f_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_List_modifyTailIdx_go___redArg(v_f_5384_, v_i_5383_, v_l_5382_);
    return v___x_5385_;
}
pub unsafe fn l_List_modifyTailIdx___redArg___boxed(
    mut v_l_5386_: *mut crate::leanh::LeanObject,
    mut v_i_5387_: *mut crate::leanh::LeanObject,
    mut v_f_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5389_ = l_List_modifyTailIdx___redArg(v_l_5386_, v_i_5387_, v_f_5388_);
    crate::leanh::lean_dec(v_i_5387_);
    return v_res_5389_;
}
pub unsafe fn l_List_modifyTailIdx(
    mut v_00_u03b1_5390_: *mut crate::leanh::LeanObject,
    mut v_l_5391_: *mut crate::leanh::LeanObject,
    mut v_i_5392_: *mut crate::leanh::LeanObject,
    mut v_f_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_List_modifyTailIdx_go___redArg(v_f_5393_, v_i_5392_, v_l_5391_);
    return v___x_5394_;
}
pub unsafe fn l_List_modifyTailIdx___boxed(
    mut v_00_u03b1_5395_: *mut crate::leanh::LeanObject,
    mut v_l_5396_: *mut crate::leanh::LeanObject,
    mut v_i_5397_: *mut crate::leanh::LeanObject,
    mut v_f_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5399_ = l_List_modifyTailIdx(v_00_u03b1_5395_, v_l_5396_, v_i_5397_, v_f_5398_);
    crate::leanh::lean_dec(v_i_5397_);
    return v_res_5399_;
}
pub unsafe fn l_List_modifyHead___redArg(
    mut v_f_5400_: *mut crate::leanh::LeanObject,
    mut v_x_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5401_) == 0 {
                    crate::leanh::lean_dec(v_f_5400_);
                    return v_x_5401_;
                } else {
                    v_head_5402_ = crate::leanh::lean_ctor_get(v_x_5401_, 0);
                    v_tail_5403_ = crate::leanh::lean_ctor_get(v_x_5401_, 1);
                    v_isSharedCheck_5411_ = (!crate::leanh::lean_is_exclusive(v_x_5401_)) as u8;
                    if v_isSharedCheck_5411_ == 0 {
                        v___x_5405_ = v_x_5401_;
                        v_isShared_5406_ = v_isSharedCheck_5411_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5403_);
                        crate::leanh::lean_inc(v_head_5402_);
                        crate::leanh::lean_dec(v_x_5401_);
                        v___x_5405_ = crate::leanh::lean_box(0);
                        v_isShared_5406_ = v_isSharedCheck_5411_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5407_ = crate::leanh::lean_apply_1(v_f_5400_, v_head_5402_);
                if v_isShared_5406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5405_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5410_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_tail_5403_);
                    v___x_5409_ = v_reuseFailAlloc_5410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_modifyHead(
    mut v_00_u03b1_5412_: *mut crate::leanh::LeanObject,
    mut v_f_5413_: *mut crate::leanh::LeanObject,
    mut v_x_5414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5414_) == 0 {
                    crate::leanh::lean_dec(v_f_5413_);
                    return v_x_5414_;
                } else {
                    v_head_5415_ = crate::leanh::lean_ctor_get(v_x_5414_, 0);
                    v_tail_5416_ = crate::leanh::lean_ctor_get(v_x_5414_, 1);
                    v_isSharedCheck_5424_ = (!crate::leanh::lean_is_exclusive(v_x_5414_)) as u8;
                    if v_isSharedCheck_5424_ == 0 {
                        v___x_5418_ = v_x_5414_;
                        v_isShared_5419_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5416_);
                        crate::leanh::lean_inc(v_head_5415_);
                        crate::leanh::lean_dec(v_x_5414_);
                        v___x_5418_ = crate::leanh::lean_box(0);
                        v_isShared_5419_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5420_ = crate::leanh::lean_apply_1(v_f_5413_, v_head_5415_);
                if v_isShared_5419_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5418_, 0, v___x_5420_);
                    v___x_5422_ = v___x_5418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_tail_5416_);
                    v___x_5422_ = v_reuseFailAlloc_5423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_modify___redArg(
    mut v_l_5425_: *mut crate::leanh::LeanObject,
    mut v_i_5426_: *mut crate::leanh::LeanObject,
    mut v_f_5427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5428_ =
        crate::leanh::lean_alloc_closure(l_List_modifyHead as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_5428_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5428_, 1, v_f_5427_);
    v___x_5429_ = l_List_modifyTailIdx_go___redArg(v___x_5428_, v_i_5426_, v_l_5425_);
    return v___x_5429_;
}
pub unsafe fn l_List_modify___redArg___boxed(
    mut v_l_5430_: *mut crate::leanh::LeanObject,
    mut v_i_5431_: *mut crate::leanh::LeanObject,
    mut v_f_5432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5433_ = l_List_modify___redArg(v_l_5430_, v_i_5431_, v_f_5432_);
    crate::leanh::lean_dec(v_i_5431_);
    return v_res_5433_;
}
pub unsafe fn l_List_modify(
    mut v_00_u03b1_5434_: *mut crate::leanh::LeanObject,
    mut v_l_5435_: *mut crate::leanh::LeanObject,
    mut v_i_5436_: *mut crate::leanh::LeanObject,
    mut v_f_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ =
        crate::leanh::lean_alloc_closure(l_List_modifyHead as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_5438_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5438_, 1, v_f_5437_);
    v___x_5439_ = l_List_modifyTailIdx_go___redArg(v___x_5438_, v_i_5436_, v_l_5435_);
    return v___x_5439_;
}
pub unsafe fn l_List_modify___boxed(
    mut v_00_u03b1_5440_: *mut crate::leanh::LeanObject,
    mut v_l_5441_: *mut crate::leanh::LeanObject,
    mut v_i_5442_: *mut crate::leanh::LeanObject,
    mut v_f_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ = l_List_modify(v_00_u03b1_5440_, v_l_5441_, v_i_5442_, v_f_5443_);
    crate::leanh::lean_dec(v_i_5442_);
    return v_res_5444_;
}
pub unsafe fn l_List_insert___redArg(
    mut v_inst_5445_: *mut crate::leanh::LeanObject,
    mut v_a_5446_: *mut crate::leanh::LeanObject,
    mut v_l_5447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5448_: u8 = 0;
    crate::leanh::lean_inc(v_l_5447_);
    crate::leanh::lean_inc(v_a_5446_);
    v___x_5448_ = l_List_elem___redArg(v_inst_5445_, v_a_5446_, v_l_5447_);
    if v___x_5448_ == 0 {
        let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5449_, 0, v_a_5446_);
        crate::leanh::lean_ctor_set(v___x_5449_, 1, v_l_5447_);
        return v___x_5449_;
    } else {
        crate::leanh::lean_dec(v_a_5446_);
        return v_l_5447_;
    }
}
pub unsafe fn l_List_insert(
    mut v_00_u03b1_5450_: *mut crate::leanh::LeanObject,
    mut v_inst_5451_: *mut crate::leanh::LeanObject,
    mut v_a_5452_: *mut crate::leanh::LeanObject,
    mut v_l_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5454_: u8 = 0;
    crate::leanh::lean_inc(v_l_5453_);
    crate::leanh::lean_inc(v_a_5452_);
    v___x_5454_ = l_List_elem___redArg(v_inst_5451_, v_a_5452_, v_l_5453_);
    if v___x_5454_ == 0 {
        let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5455_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5455_, 0, v_a_5452_);
        crate::leanh::lean_ctor_set(v___x_5455_, 1, v_l_5453_);
        return v___x_5455_;
    } else {
        crate::leanh::lean_dec(v_a_5452_);
        return v_l_5453_;
    }
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5460_: u8 = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v_one_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5459_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5460_ = lean_nat_dec_eq(v_a_5457_, v_zero_5459_);
                if v_isZero_5460_ == 1 {
                    v___x_5461_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5461_, 0, v_a_5456_);
                    crate::leanh::lean_ctor_set(v___x_5461_, 1, v_a_5458_);
                    return v___x_5461_;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_5458_) == 0 {
                        crate::leanh::lean_dec(v_a_5456_);
                        return v_a_5458_;
                    } else {
                        v_head_5462_ = crate::leanh::lean_ctor_get(v_a_5458_, 0);
                        v_tail_5463_ = crate::leanh::lean_ctor_get(v_a_5458_, 1);
                        v_isSharedCheck_5473_ = (!crate::leanh::lean_is_exclusive(v_a_5458_)) as u8;
                        if v_isSharedCheck_5473_ == 0 {
                            v___x_5465_ = v_a_5458_;
                            v_isShared_5466_ = v_isSharedCheck_5473_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_5463_);
                            crate::leanh::lean_inc(v_head_5462_);
                            crate::leanh::lean_dec(v_a_5458_);
                            v___x_5465_ = crate::leanh::lean_box(0);
                            v_isShared_5466_ = v_isSharedCheck_5473_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5467_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_5468_ = lean_nat_sub(v_a_5457_, v_one_5467_);
                v___x_5469_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
                    v_a_5456_,
                    v_n_5468_,
                    v_tail_5463_,
                );
                crate::leanh::lean_dec(v_n_5468_);
                if v_isShared_5466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5465_, 1, v___x_5469_);
                    v___x_5471_ = v___x_5465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_head_5462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 1, v___x_5469_);
                    v___x_5471_ = v_reuseFailAlloc_5472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg___boxed(
    mut v_a_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5474_, v_a_5475_, v_a_5476_,
    );
    crate::leanh::lean_dec(v_a_5475_);
    return v_res_5477_;
}
pub unsafe fn l_List_insertIdx___redArg(
    mut v_xs_5478_: *mut crate::leanh::LeanObject,
    mut v_i_5479_: *mut crate::leanh::LeanObject,
    mut v_a_5480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5481_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5480_, v_i_5479_, v_xs_5478_,
    );
    return v___x_5481_;
}
pub unsafe fn l_List_insertIdx___redArg___boxed(
    mut v_xs_5482_: *mut crate::leanh::LeanObject,
    mut v_i_5483_: *mut crate::leanh::LeanObject,
    mut v_a_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_List_insertIdx___redArg(v_xs_5482_, v_i_5483_, v_a_5484_);
    crate::leanh::lean_dec(v_i_5483_);
    return v_res_5485_;
}
pub unsafe fn l_List_insertIdx(
    mut v_00_u03b1_5486_: *mut crate::leanh::LeanObject,
    mut v_xs_5487_: *mut crate::leanh::LeanObject,
    mut v_i_5488_: *mut crate::leanh::LeanObject,
    mut v_a_5489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5489_, v_i_5488_, v_xs_5487_,
    );
    return v___x_5490_;
}
pub unsafe fn l_List_insertIdx___boxed(
    mut v_00_u03b1_5491_: *mut crate::leanh::LeanObject,
    mut v_xs_5492_: *mut crate::leanh::LeanObject,
    mut v_i_5493_: *mut crate::leanh::LeanObject,
    mut v_a_5494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5495_ = l_List_insertIdx(v_00_u03b1_5491_, v_xs_5492_, v_i_5493_, v_a_5494_);
    crate::leanh::lean_dec(v_i_5493_);
    return v_res_5495_;
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(
    mut v_00_u03b1_5496_: *mut crate::leanh::LeanObject,
    mut v_a_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: *mut crate::leanh::LeanObject,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5500_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5497_, v_a_5498_, v_a_5499_,
    );
    return v___x_5500_;
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(
    mut v_00_u03b1_5501_: *mut crate::leanh::LeanObject,
    mut v_a_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5505_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(
        v_00_u03b1_5501_,
        v_a_5502_,
        v_a_5503_,
        v_a_5504_,
    );
    crate::leanh::lean_dec(v_a_5503_);
    return v_res_5505_;
}
pub unsafe fn l_List_erase___redArg(
    mut v_inst_5506_: *mut crate::leanh::LeanObject,
    mut v_x_5507_: *mut crate::leanh::LeanObject,
    mut v_x_5508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5507_) == 0 {
                    crate::leanh::lean_dec(v_x_5508_);
                    crate::leanh::lean_dec_ref(v_inst_5506_);
                    return v_x_5507_;
                } else {
                    v_head_5509_ = crate::leanh::lean_ctor_get(v_x_5507_, 0);
                    v_tail_5510_ = crate::leanh::lean_ctor_get(v_x_5507_, 1);
                    v_isSharedCheck_5520_ = (!crate::leanh::lean_is_exclusive(v_x_5507_)) as u8;
                    if v_isSharedCheck_5520_ == 0 {
                        v___x_5512_ = v_x_5507_;
                        v_isShared_5513_ = v_isSharedCheck_5520_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5510_);
                        crate::leanh::lean_inc(v_head_5509_);
                        crate::leanh::lean_dec(v_x_5507_);
                        v___x_5512_ = crate::leanh::lean_box(0);
                        v_isShared_5513_ = v_isSharedCheck_5520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_5506_);
                crate::leanh::lean_inc(v_x_5508_);
                crate::leanh::lean_inc(v_head_5509_);
                v___x_5514_ = crate::leanh::lean_apply_2(v_inst_5506_, v_head_5509_, v_x_5508_);
                v___x_5515_ = (crate::leanh::lean_unbox(v___x_5514_) as u8);
                if v___x_5515_ == 0 {
                    v___x_5516_ = l_List_erase___redArg(v_inst_5506_, v_tail_5510_, v_x_5508_);
                    if v_isShared_5513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5512_, 1, v___x_5516_);
                        v___x_5518_ = v___x_5512_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5519_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_head_5509_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5516_);
                        v___x_5518_ = v_reuseFailAlloc_5519_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5512_);
                    crate::leanh::lean_dec(v_head_5509_);
                    crate::leanh::lean_dec(v_x_5508_);
                    crate::leanh::lean_dec_ref(v_inst_5506_);
                    return v_tail_5510_;
                }
            }
            2 => {
                return v___x_5518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_erase(
    mut v_00_u03b1_5521_: *mut crate::leanh::LeanObject,
    mut v_inst_5522_: *mut crate::leanh::LeanObject,
    mut v_x_5523_: *mut crate::leanh::LeanObject,
    mut v_x_5524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5525_ = l_List_erase___redArg(v_inst_5522_, v_x_5523_, v_x_5524_);
    return v___x_5525_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(
    mut v_x_5526_: *mut crate::leanh::LeanObject,
    mut v_x_5527_: *mut crate::leanh::LeanObject,
    mut v_h__1_5528_: *mut crate::leanh::LeanObject,
    mut v_h__2_5529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5526_) == 0 {
        let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5529_);
        v___x_5530_ = crate::leanh::lean_apply_1(v_h__1_5528_, v_x_5527_);
        return v___x_5530_;
    } else {
        let mut v_head_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5528_);
        v_head_5531_ = crate::leanh::lean_ctor_get(v_x_5526_, 0);
        crate::leanh::lean_inc(v_head_5531_);
        v_tail_5532_ = crate::leanh::lean_ctor_get(v_x_5526_, 1);
        crate::leanh::lean_inc(v_tail_5532_);
        crate::leanh::lean_dec_ref_known(v_x_5526_, 2);
        v___x_5533_ =
            crate::leanh::lean_apply_3(v_h__2_5529_, v_head_5531_, v_tail_5532_, v_x_5527_);
        return v___x_5533_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(
    mut v_00_u03b1_5534_: *mut crate::leanh::LeanObject,
    mut v_motive_5535_: *mut crate::leanh::LeanObject,
    mut v_x_5536_: *mut crate::leanh::LeanObject,
    mut v_x_5537_: *mut crate::leanh::LeanObject,
    mut v_h__1_5538_: *mut crate::leanh::LeanObject,
    mut v_h__2_5539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5536_) == 0 {
        let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_5539_);
        v___x_5540_ = crate::leanh::lean_apply_1(v_h__1_5538_, v_x_5537_);
        return v___x_5540_;
    } else {
        let mut v_head_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_5538_);
        v_head_5541_ = crate::leanh::lean_ctor_get(v_x_5536_, 0);
        crate::leanh::lean_inc(v_head_5541_);
        v_tail_5542_ = crate::leanh::lean_ctor_get(v_x_5536_, 1);
        crate::leanh::lean_inc(v_tail_5542_);
        crate::leanh::lean_dec_ref_known(v_x_5536_, 2);
        v___x_5543_ =
            crate::leanh::lean_apply_3(v_h__2_5539_, v_head_5541_, v_tail_5542_, v_x_5537_);
        return v___x_5543_;
    }
}
pub unsafe fn l_List_eraseP___redArg(
    mut v_p_5544_: *mut crate::leanh::LeanObject,
    mut v_x_5545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5545_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_5544_);
                    return v_x_5545_;
                } else {
                    v_head_5546_ = crate::leanh::lean_ctor_get(v_x_5545_, 0);
                    v_tail_5547_ = crate::leanh::lean_ctor_get(v_x_5545_, 1);
                    v_isSharedCheck_5557_ = (!crate::leanh::lean_is_exclusive(v_x_5545_)) as u8;
                    if v_isSharedCheck_5557_ == 0 {
                        v___x_5549_ = v_x_5545_;
                        v_isShared_5550_ = v_isSharedCheck_5557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5547_);
                        crate::leanh::lean_inc(v_head_5546_);
                        crate::leanh::lean_dec(v_x_5545_);
                        v___x_5549_ = crate::leanh::lean_box(0);
                        v_isShared_5550_ = v_isSharedCheck_5557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_p_5544_);
                crate::leanh::lean_inc(v_head_5546_);
                v___x_5551_ = crate::leanh::lean_apply_1(v_p_5544_, v_head_5546_);
                v___x_5552_ = (crate::leanh::lean_unbox(v___x_5551_) as u8);
                if v___x_5552_ == 0 {
                    v___x_5553_ = l_List_eraseP___redArg(v_p_5544_, v_tail_5547_);
                    if v_isShared_5550_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5549_, 1, v___x_5553_);
                        v___x_5555_ = v___x_5549_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5556_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_head_5546_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5553_);
                        v___x_5555_ = v_reuseFailAlloc_5556_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5549_);
                    crate::leanh::lean_dec(v_head_5546_);
                    crate::leanh::lean_dec_ref(v_p_5544_);
                    return v_tail_5547_;
                }
            }
            2 => {
                return v___x_5555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_eraseP(
    mut v_00_u03b1_5558_: *mut crate::leanh::LeanObject,
    mut v_p_5559_: *mut crate::leanh::LeanObject,
    mut v_x_5560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5561_ = l_List_eraseP___redArg(v_p_5559_, v_x_5560_);
    return v___x_5561_;
}
pub unsafe fn l_List_eraseIdx___redArg(
    mut v_x_5562_: *mut crate::leanh::LeanObject,
    mut v_x_5563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v_zero_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5570_: u8 = 0;
    let mut v_one_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5562_) == 0 {
                    return v_x_5562_;
                } else {
                    v_head_5564_ = crate::leanh::lean_ctor_get(v_x_5562_, 0);
                    v_tail_5565_ = crate::leanh::lean_ctor_get(v_x_5562_, 1);
                    v_isSharedCheck_5577_ = (!crate::leanh::lean_is_exclusive(v_x_5562_)) as u8;
                    if v_isSharedCheck_5577_ == 0 {
                        v___x_5567_ = v_x_5562_;
                        v_isShared_5568_ = v_isSharedCheck_5577_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5565_);
                        crate::leanh::lean_inc(v_head_5564_);
                        crate::leanh::lean_dec(v_x_5562_);
                        v___x_5567_ = crate::leanh::lean_box(0);
                        v_isShared_5568_ = v_isSharedCheck_5577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_5569_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5570_ = lean_nat_dec_eq(v_x_5563_, v_zero_5569_);
                if v_isZero_5570_ == 1 {
                    crate::leanh::lean_del_object(v___x_5567_);
                    crate::leanh::lean_dec(v_head_5564_);
                    return v_tail_5565_;
                } else {
                    v_one_5571_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_5572_ = lean_nat_sub(v_x_5563_, v_one_5571_);
                    v___x_5573_ = l_List_eraseIdx___redArg(v_tail_5565_, v_n_5572_);
                    crate::leanh::lean_dec(v_n_5572_);
                    if v_isShared_5568_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5567_, 1, v___x_5573_);
                        v___x_5575_ = v___x_5567_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5576_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_head_5564_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5573_);
                        v___x_5575_ = v_reuseFailAlloc_5576_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_eraseIdx___redArg___boxed(
    mut v_x_5578_: *mut crate::leanh::LeanObject,
    mut v_x_5579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5580_ = l_List_eraseIdx___redArg(v_x_5578_, v_x_5579_);
    crate::leanh::lean_dec(v_x_5579_);
    return v_res_5580_;
}
pub unsafe fn l_List_eraseIdx(
    mut v_00_u03b1_5581_: *mut crate::leanh::LeanObject,
    mut v_x_5582_: *mut crate::leanh::LeanObject,
    mut v_x_5583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5584_ = l_List_eraseIdx___redArg(v_x_5582_, v_x_5583_);
    return v___x_5584_;
}
pub unsafe fn l_List_eraseIdx___boxed(
    mut v_00_u03b1_5585_: *mut crate::leanh::LeanObject,
    mut v_x_5586_: *mut crate::leanh::LeanObject,
    mut v_x_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5588_ = l_List_eraseIdx(v_00_u03b1_5585_, v_x_5586_, v_x_5587_);
    crate::leanh::lean_dec(v_x_5587_);
    return v_res_5588_;
}
pub unsafe fn l_List_find_x3f___redArg(
    mut v_p_5589_: *mut crate::leanh::LeanObject,
    mut v_x_5590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5590_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_5589_);
                    v___x_5591_ = crate::leanh::lean_box(0);
                    return v___x_5591_;
                } else {
                    v_head_5592_ = crate::leanh::lean_ctor_get(v_x_5590_, 0);
                    crate::leanh::lean_inc_n(v_head_5592_, 2);
                    v_tail_5593_ = crate::leanh::lean_ctor_get(v_x_5590_, 1);
                    crate::leanh::lean_inc(v_tail_5593_);
                    crate::leanh::lean_dec_ref_known(v_x_5590_, 2);
                    crate::leanh::lean_inc_ref(v_p_5589_);
                    v___x_5594_ = crate::leanh::lean_apply_1(v_p_5589_, v_head_5592_);
                    v___x_5595_ = (crate::leanh::lean_unbox(v___x_5594_) as u8);
                    if v___x_5595_ == 0 {
                        crate::leanh::lean_dec(v_head_5592_);
                        v_x_5590_ = v_tail_5593_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5593_);
                        crate::leanh::lean_dec_ref(v_p_5589_);
                        v___x_5597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5597_, 0, v_head_5592_);
                        return v___x_5597_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f(
    mut v_00_u03b1_5598_: *mut crate::leanh::LeanObject,
    mut v_p_5599_: *mut crate::leanh::LeanObject,
    mut v_x_5600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5601_ = l_List_find_x3f___redArg(v_p_5599_, v_x_5600_);
    return v___x_5601_;
}
pub unsafe fn l_List_findSome_x3f___redArg(
    mut v_f_5602_: *mut crate::leanh::LeanObject,
    mut v_x_5603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5603_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_5602_);
                    v___x_5604_ = crate::leanh::lean_box(0);
                    return v___x_5604_;
                } else {
                    v_head_5605_ = crate::leanh::lean_ctor_get(v_x_5603_, 0);
                    crate::leanh::lean_inc(v_head_5605_);
                    v_tail_5606_ = crate::leanh::lean_ctor_get(v_x_5603_, 1);
                    crate::leanh::lean_inc(v_tail_5606_);
                    crate::leanh::lean_dec_ref_known(v_x_5603_, 2);
                    crate::leanh::lean_inc_ref(v_f_5602_);
                    v___x_5607_ = crate::leanh::lean_apply_1(v_f_5602_, v_head_5605_);
                    if crate::leanh::lean_obj_tag(v___x_5607_) == 0 {
                        v_x_5603_ = v_tail_5606_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5606_);
                        crate::leanh::lean_dec_ref(v_f_5602_);
                        return v___x_5607_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findSome_x3f(
    mut v_00_u03b1_5609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5610_: *mut crate::leanh::LeanObject,
    mut v_f_5611_: *mut crate::leanh::LeanObject,
    mut v_x_5612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_List_findSome_x3f___redArg(v_f_5611_, v_x_5612_);
    return v___x_5613_;
}
pub unsafe fn l_List_findRev_x3f___redArg(
    mut v_p_5614_: *mut crate::leanh::LeanObject,
    mut v_x_5615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5615_) == 0 {
        let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_5614_);
        v___x_5616_ = crate::leanh::lean_box(0);
        return v___x_5616_;
    } else {
        let mut v_head_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_5617_ = crate::leanh::lean_ctor_get(v_x_5615_, 0);
        crate::leanh::lean_inc(v_head_5617_);
        v_tail_5618_ = crate::leanh::lean_ctor_get(v_x_5615_, 1);
        crate::leanh::lean_inc(v_tail_5618_);
        crate::leanh::lean_dec_ref_known(v_x_5615_, 2);
        crate::leanh::lean_inc_ref(v_p_5614_);
        v___x_5619_ = l_List_findRev_x3f___redArg(v_p_5614_, v_tail_5618_);
        if crate::leanh::lean_obj_tag(v___x_5619_) == 0 {
            let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5621_: u8 = 0;
            crate::leanh::lean_inc(v_head_5617_);
            v___x_5620_ = crate::leanh::lean_apply_1(v_p_5614_, v_head_5617_);
            v___x_5621_ = (crate::leanh::lean_unbox(v___x_5620_) as u8);
            if v___x_5621_ == 0 {
                crate::leanh::lean_dec(v_head_5617_);
                return v___x_5619_;
            } else {
                let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5622_, 0, v_head_5617_);
                return v___x_5622_;
            }
        } else {
            crate::leanh::lean_dec(v_head_5617_);
            crate::leanh::lean_dec_ref(v_p_5614_);
            return v___x_5619_;
        }
    }
}
pub unsafe fn l_List_findRev_x3f(
    mut v_00_u03b1_5623_: *mut crate::leanh::LeanObject,
    mut v_p_5624_: *mut crate::leanh::LeanObject,
    mut v_x_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5626_ = l_List_findRev_x3f___redArg(v_p_5624_, v_x_5625_);
    return v___x_5626_;
}
pub unsafe fn l_List_findSomeRev_x3f___redArg(
    mut v_f_5627_: *mut crate::leanh::LeanObject,
    mut v_x_5628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5628_) == 0 {
        let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_5627_);
        v___x_5629_ = crate::leanh::lean_box(0);
        return v___x_5629_;
    } else {
        let mut v_head_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_5630_ = crate::leanh::lean_ctor_get(v_x_5628_, 0);
        crate::leanh::lean_inc(v_head_5630_);
        v_tail_5631_ = crate::leanh::lean_ctor_get(v_x_5628_, 1);
        crate::leanh::lean_inc(v_tail_5631_);
        crate::leanh::lean_dec_ref_known(v_x_5628_, 2);
        crate::leanh::lean_inc_ref(v_f_5627_);
        v___x_5632_ = l_List_findSomeRev_x3f___redArg(v_f_5627_, v_tail_5631_);
        if crate::leanh::lean_obj_tag(v___x_5632_) == 0 {
            let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5633_ = crate::leanh::lean_apply_1(v_f_5627_, v_head_5630_);
            return v___x_5633_;
        } else {
            crate::leanh::lean_dec(v_head_5630_);
            crate::leanh::lean_dec_ref(v_f_5627_);
            return v___x_5632_;
        }
    }
}
pub unsafe fn l_List_findSomeRev_x3f(
    mut v_00_u03b1_5634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5635_: *mut crate::leanh::LeanObject,
    mut v_f_5636_: *mut crate::leanh::LeanObject,
    mut v_x_5637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5638_ = l_List_findSomeRev_x3f___redArg(v_f_5636_, v_x_5637_);
    return v___x_5638_;
}
pub unsafe fn l_List_findIdx_go___redArg(
    mut v_p_5639_: *mut crate::leanh::LeanObject,
    mut v_a_5640_: *mut crate::leanh::LeanObject,
    mut v_a_5641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5640_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_5639_);
                    return v_a_5641_;
                } else {
                    v_head_5642_ = crate::leanh::lean_ctor_get(v_a_5640_, 0);
                    crate::leanh::lean_inc(v_head_5642_);
                    v_tail_5643_ = crate::leanh::lean_ctor_get(v_a_5640_, 1);
                    crate::leanh::lean_inc(v_tail_5643_);
                    crate::leanh::lean_dec_ref_known(v_a_5640_, 2);
                    crate::leanh::lean_inc_ref(v_p_5639_);
                    v___x_5644_ = crate::leanh::lean_apply_1(v_p_5639_, v_head_5642_);
                    v___x_5645_ = (crate::leanh::lean_unbox(v___x_5644_) as u8);
                    if v___x_5645_ == 0 {
                        v___x_5646_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5647_ = lean_nat_add(v_a_5641_, v___x_5646_);
                        crate::leanh::lean_dec(v_a_5641_);
                        v_a_5640_ = v_tail_5643_;
                        v_a_5641_ = v___x_5647_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5643_);
                        crate::leanh::lean_dec_ref(v_p_5639_);
                        return v_a_5641_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findIdx_go(
    mut v_00_u03b1_5649_: *mut crate::leanh::LeanObject,
    mut v_p_5650_: *mut crate::leanh::LeanObject,
    mut v_a_5651_: *mut crate::leanh::LeanObject,
    mut v_a_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5653_ = l_List_findIdx_go___redArg(v_p_5650_, v_a_5651_, v_a_5652_);
    return v___x_5653_;
}
pub unsafe fn l_List_findIdx___redArg(
    mut v_p_5654_: *mut crate::leanh::LeanObject,
    mut v_l_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5656_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5657_ = l_List_findIdx_go___redArg(v_p_5654_, v_l_5655_, v___x_5656_);
    return v___x_5657_;
}
pub unsafe fn l_List_findIdx(
    mut v_00_u03b1_5658_: *mut crate::leanh::LeanObject,
    mut v_p_5659_: *mut crate::leanh::LeanObject,
    mut v_l_5660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5661_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5662_ = l_List_findIdx_go___redArg(v_p_5659_, v_l_5660_, v___x_5661_);
    return v___x_5662_;
}
pub unsafe fn l_List_idxOf___redArg___lam__0(
    mut v_inst_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
    mut v_x_5665_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    v___x_5666_ = crate::leanh::lean_apply_2(v_inst_5663_, v_x_5665_, v_a_5664_);
    v___x_5667_ = (crate::leanh::lean_unbox(v___x_5666_) as u8);
    return v___x_5667_;
}
pub unsafe fn l_List_idxOf___redArg___lam__0___boxed(
    mut v_inst_5668_: *mut crate::leanh::LeanObject,
    mut v_a_5669_: *mut crate::leanh::LeanObject,
    mut v_x_5670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5671_: u8 = 0;
    let mut v_r_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5671_ = l_List_idxOf___redArg___lam__0(v_inst_5668_, v_a_5669_, v_x_5670_);
    v_r_5672_ = crate::leanh::lean_box((v_res_5671_) as usize);
    return v_r_5672_;
}
pub unsafe fn l_List_idxOf___redArg(
    mut v_inst_5673_: *mut crate::leanh::LeanObject,
    mut v_a_5674_: *mut crate::leanh::LeanObject,
    mut v_l_5675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5676_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5676_, 0, v_inst_5673_);
    crate::leanh::lean_closure_set(v___f_5676_, 1, v_a_5674_);
    v___x_5677_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5678_ = l_List_findIdx_go___redArg(v___f_5676_, v_l_5675_, v___x_5677_);
    return v___x_5678_;
}
pub unsafe fn l_List_idxOf(
    mut v_00_u03b1_5679_: *mut crate::leanh::LeanObject,
    mut v_inst_5680_: *mut crate::leanh::LeanObject,
    mut v_a_5681_: *mut crate::leanh::LeanObject,
    mut v_l_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5683_ = l_List_idxOf___redArg(v_inst_5680_, v_a_5681_, v_l_5682_);
    return v___x_5683_;
}
pub unsafe fn l_List_findIdx_x3f_go___redArg(
    mut v_p_5684_: *mut crate::leanh::LeanObject,
    mut v_a_5685_: *mut crate::leanh::LeanObject,
    mut v_a_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5685_) == 0 {
                    crate::leanh::lean_dec(v_a_5686_);
                    crate::leanh::lean_dec_ref(v_p_5684_);
                    v___x_5687_ = crate::leanh::lean_box(0);
                    return v___x_5687_;
                } else {
                    v_head_5688_ = crate::leanh::lean_ctor_get(v_a_5685_, 0);
                    crate::leanh::lean_inc(v_head_5688_);
                    v_tail_5689_ = crate::leanh::lean_ctor_get(v_a_5685_, 1);
                    crate::leanh::lean_inc(v_tail_5689_);
                    crate::leanh::lean_dec_ref_known(v_a_5685_, 2);
                    crate::leanh::lean_inc_ref(v_p_5684_);
                    v___x_5690_ = crate::leanh::lean_apply_1(v_p_5684_, v_head_5688_);
                    v___x_5691_ = (crate::leanh::lean_unbox(v___x_5690_) as u8);
                    if v___x_5691_ == 0 {
                        v___x_5692_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5693_ = lean_nat_add(v_a_5686_, v___x_5692_);
                        crate::leanh::lean_dec(v_a_5686_);
                        v_a_5685_ = v_tail_5689_;
                        v_a_5686_ = v___x_5693_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5689_);
                        crate::leanh::lean_dec_ref(v_p_5684_);
                        v___x_5695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5695_, 0, v_a_5686_);
                        return v___x_5695_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findIdx_x3f_go(
    mut v_00_u03b1_5696_: *mut crate::leanh::LeanObject,
    mut v_p_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_List_findIdx_x3f_go___redArg(v_p_5697_, v_a_5698_, v_a_5699_);
    return v___x_5700_;
}
pub unsafe fn l_List_findIdx_x3f___redArg(
    mut v_p_5701_: *mut crate::leanh::LeanObject,
    mut v_l_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5704_ = l_List_findIdx_x3f_go___redArg(v_p_5701_, v_l_5702_, v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn l_List_findIdx_x3f(
    mut v_00_u03b1_5705_: *mut crate::leanh::LeanObject,
    mut v_p_5706_: *mut crate::leanh::LeanObject,
    mut v_l_5707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5708_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5709_ = l_List_findIdx_x3f_go___redArg(v_p_5706_, v_l_5707_, v___x_5708_);
    return v___x_5709_;
}
pub unsafe fn l_List_idxOf_x3f___redArg(
    mut v_inst_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_l_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5713_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5713_, 0, v_inst_5710_);
    crate::leanh::lean_closure_set(v___f_5713_, 1, v_a_5711_);
    v___x_5714_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5715_ = l_List_findIdx_x3f_go___redArg(v___f_5713_, v_l_5712_, v___x_5714_);
    return v___x_5715_;
}
pub unsafe fn l_List_idxOf_x3f(
    mut v_00_u03b1_5716_: *mut crate::leanh::LeanObject,
    mut v_inst_5717_: *mut crate::leanh::LeanObject,
    mut v_a_5718_: *mut crate::leanh::LeanObject,
    mut v_l_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5720_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5720_, 0, v_inst_5717_);
    crate::leanh::lean_closure_set(v___f_5720_, 1, v_a_5718_);
    v___x_5721_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5722_ = l_List_findIdx_x3f_go___redArg(v___f_5720_, v_l_5719_, v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn l_List_findFinIdx_x3f_go___redArg(
    mut v_p_5723_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5724_: *mut crate::leanh::LeanObject,
    mut v_i_5725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: u8 = 0;
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_l_x27_5724_) == 0 {
                    crate::leanh::lean_dec(v_i_5725_);
                    crate::leanh::lean_dec_ref(v_p_5723_);
                    v___x_5726_ = crate::leanh::lean_box(0);
                    return v___x_5726_;
                } else {
                    v_head_5727_ = crate::leanh::lean_ctor_get(v_l_x27_5724_, 0);
                    crate::leanh::lean_inc(v_head_5727_);
                    v_tail_5728_ = crate::leanh::lean_ctor_get(v_l_x27_5724_, 1);
                    crate::leanh::lean_inc(v_tail_5728_);
                    crate::leanh::lean_dec_ref_known(v_l_x27_5724_, 2);
                    crate::leanh::lean_inc_ref(v_p_5723_);
                    v___x_5729_ = crate::leanh::lean_apply_1(v_p_5723_, v_head_5727_);
                    v___x_5730_ = (crate::leanh::lean_unbox(v___x_5729_) as u8);
                    if v___x_5730_ == 0 {
                        v___x_5731_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5732_ = lean_nat_add(v_i_5725_, v___x_5731_);
                        crate::leanh::lean_dec(v_i_5725_);
                        v_l_x27_5724_ = v_tail_5728_;
                        v_i_5725_ = v___x_5732_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5728_);
                        crate::leanh::lean_dec_ref(v_p_5723_);
                        v___x_5734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5734_, 0, v_i_5725_);
                        return v___x_5734_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findFinIdx_x3f_go(
    mut v_00_u03b1_5735_: *mut crate::leanh::LeanObject,
    mut v_p_5736_: *mut crate::leanh::LeanObject,
    mut v_l_5737_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5738_: *mut crate::leanh::LeanObject,
    mut v_i_5739_: *mut crate::leanh::LeanObject,
    mut v_h_5740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ = l_List_findFinIdx_x3f_go___redArg(v_p_5736_, v_l_x27_5738_, v_i_5739_);
    return v___x_5741_;
}
pub unsafe fn l_List_findFinIdx_x3f_go___boxed(
    mut v_00_u03b1_5742_: *mut crate::leanh::LeanObject,
    mut v_p_5743_: *mut crate::leanh::LeanObject,
    mut v_l_5744_: *mut crate::leanh::LeanObject,
    mut v_l_x27_5745_: *mut crate::leanh::LeanObject,
    mut v_i_5746_: *mut crate::leanh::LeanObject,
    mut v_h_5747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_List_findFinIdx_x3f_go(
        v_00_u03b1_5742_,
        v_p_5743_,
        v_l_5744_,
        v_l_x27_5745_,
        v_i_5746_,
        v_h_5747_,
    );
    crate::leanh::lean_dec(v_l_5744_);
    return v_res_5748_;
}
pub unsafe fn l_List_findFinIdx_x3f___redArg(
    mut v_p_5749_: *mut crate::leanh::LeanObject,
    mut v_l_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5752_ = l_List_findFinIdx_x3f_go___redArg(v_p_5749_, v_l_5750_, v___x_5751_);
    return v___x_5752_;
}
pub unsafe fn l_List_findFinIdx_x3f(
    mut v_00_u03b1_5753_: *mut crate::leanh::LeanObject,
    mut v_p_5754_: *mut crate::leanh::LeanObject,
    mut v_l_5755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5757_ = l_List_findFinIdx_x3f_go___redArg(v_p_5754_, v_l_5755_, v___x_5756_);
    return v___x_5757_;
}
pub unsafe fn l_List_finIdxOf_x3f___redArg(
    mut v_inst_5758_: *mut crate::leanh::LeanObject,
    mut v_a_5759_: *mut crate::leanh::LeanObject,
    mut v_l_5760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5761_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5761_, 0, v_inst_5758_);
    crate::leanh::lean_closure_set(v___f_5761_, 1, v_a_5759_);
    v___x_5762_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5763_ = l_List_findFinIdx_x3f_go___redArg(v___f_5761_, v_l_5760_, v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn l_List_finIdxOf_x3f(
    mut v_00_u03b1_5764_: *mut crate::leanh::LeanObject,
    mut v_inst_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_l_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5768_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5768_, 0, v_inst_5765_);
    crate::leanh::lean_closure_set(v___f_5768_, 1, v_a_5766_);
    v___x_5769_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5770_ = l_List_findFinIdx_x3f_go___redArg(v___f_5768_, v_l_5767_, v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l_List_countP_go___redArg(
    mut v_p_5771_: *mut crate::leanh::LeanObject,
    mut v_a_5772_: *mut crate::leanh::LeanObject,
    mut v_a_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5772_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_5771_);
                    return v_a_5773_;
                } else {
                    v_head_5774_ = crate::leanh::lean_ctor_get(v_a_5772_, 0);
                    crate::leanh::lean_inc(v_head_5774_);
                    v_tail_5775_ = crate::leanh::lean_ctor_get(v_a_5772_, 1);
                    crate::leanh::lean_inc(v_tail_5775_);
                    crate::leanh::lean_dec_ref_known(v_a_5772_, 2);
                    crate::leanh::lean_inc_ref(v_p_5771_);
                    v___x_5776_ = crate::leanh::lean_apply_1(v_p_5771_, v_head_5774_);
                    v___x_5777_ = (crate::leanh::lean_unbox(v___x_5776_) as u8);
                    if v___x_5777_ == 0 {
                        v_a_5772_ = v_tail_5775_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5779_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5780_ = lean_nat_add(v_a_5773_, v___x_5779_);
                        crate::leanh::lean_dec(v_a_5773_);
                        v_a_5772_ = v_tail_5775_;
                        v_a_5773_ = v___x_5780_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_countP_go(
    mut v_00_u03b1_5782_: *mut crate::leanh::LeanObject,
    mut v_p_5783_: *mut crate::leanh::LeanObject,
    mut v_a_5784_: *mut crate::leanh::LeanObject,
    mut v_a_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5786_ = l_List_countP_go___redArg(v_p_5783_, v_a_5784_, v_a_5785_);
    return v___x_5786_;
}
pub unsafe fn l_List_countP___redArg(
    mut v_p_5787_: *mut crate::leanh::LeanObject,
    mut v_l_5788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5789_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5790_ = l_List_countP_go___redArg(v_p_5787_, v_l_5788_, v___x_5789_);
    return v___x_5790_;
}
pub unsafe fn l_List_countP(
    mut v_00_u03b1_5791_: *mut crate::leanh::LeanObject,
    mut v_p_5792_: *mut crate::leanh::LeanObject,
    mut v_l_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5794_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5795_ = l_List_countP_go___redArg(v_p_5792_, v_l_5793_, v___x_5794_);
    return v___x_5795_;
}
pub unsafe fn l_List_count___redArg(
    mut v_inst_5796_: *mut crate::leanh::LeanObject,
    mut v_a_5797_: *mut crate::leanh::LeanObject,
    mut v_l_5798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5799_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5799_, 0, v_inst_5796_);
    crate::leanh::lean_closure_set(v___f_5799_, 1, v_a_5797_);
    v___x_5800_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5801_ = l_List_countP_go___redArg(v___f_5799_, v_l_5798_, v___x_5800_);
    return v___x_5801_;
}
pub unsafe fn l_List_count(
    mut v_00_u03b1_5802_: *mut crate::leanh::LeanObject,
    mut v_inst_5803_: *mut crate::leanh::LeanObject,
    mut v_a_5804_: *mut crate::leanh::LeanObject,
    mut v_l_5805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5806_ = crate::leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5806_, 0, v_inst_5803_);
    crate::leanh::lean_closure_set(v___f_5806_, 1, v_a_5804_);
    v___x_5807_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5808_ = l_List_countP_go___redArg(v___f_5806_, v_l_5805_, v___x_5807_);
    return v___x_5808_;
}
pub unsafe fn l_List_lookup___redArg(
    mut v_inst_5809_: *mut crate::leanh::LeanObject,
    mut v_x_5810_: *mut crate::leanh::LeanObject,
    mut v_x_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: u8 = 0;
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5811_) == 0 {
                    crate::leanh::lean_dec(v_x_5810_);
                    crate::leanh::lean_dec_ref(v_inst_5809_);
                    v___x_5812_ = crate::leanh::lean_box(0);
                    return v___x_5812_;
                } else {
                    v_head_5813_ = crate::leanh::lean_ctor_get(v_x_5811_, 0);
                    crate::leanh::lean_inc(v_head_5813_);
                    v_tail_5814_ = crate::leanh::lean_ctor_get(v_x_5811_, 1);
                    crate::leanh::lean_inc(v_tail_5814_);
                    crate::leanh::lean_dec_ref_known(v_x_5811_, 2);
                    v_fst_5815_ = crate::leanh::lean_ctor_get(v_head_5813_, 0);
                    crate::leanh::lean_inc(v_fst_5815_);
                    v_snd_5816_ = crate::leanh::lean_ctor_get(v_head_5813_, 1);
                    crate::leanh::lean_inc(v_snd_5816_);
                    crate::leanh::lean_dec(v_head_5813_);
                    crate::leanh::lean_inc_ref(v_inst_5809_);
                    crate::leanh::lean_inc(v_x_5810_);
                    v___x_5817_ = crate::leanh::lean_apply_2(v_inst_5809_, v_x_5810_, v_fst_5815_);
                    v___x_5818_ = (crate::leanh::lean_unbox(v___x_5817_) as u8);
                    if v___x_5818_ == 0 {
                        crate::leanh::lean_dec(v_snd_5816_);
                        v_x_5811_ = v_tail_5814_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5814_);
                        crate::leanh::lean_dec(v_x_5810_);
                        crate::leanh::lean_dec_ref(v_inst_5809_);
                        v___x_5820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5820_, 0, v_snd_5816_);
                        return v___x_5820_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lookup(
    mut v_00_u03b1_5821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5822_: *mut crate::leanh::LeanObject,
    mut v_inst_5823_: *mut crate::leanh::LeanObject,
    mut v_x_5824_: *mut crate::leanh::LeanObject,
    mut v_x_5825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5826_ = l_List_lookup___redArg(v_inst_5823_, v_x_5824_, v_x_5825_);
    return v___x_5826_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5844_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0;
    v___x_5845_ = l_String_toRawSubstring_x27(v___x_5844_);
    return v___x_5845_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(
    mut v_x_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
    mut v_a_5867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: u8 = 0;
    v___x_5868_ = l_List_term___x7e___00__closed__1;
    crate::leanh::lean_inc(v_x_5865_);
    v___x_5869_ = l_Lean_Syntax_isOfKind(v_x_5865_, v___x_5868_);
    if v___x_5869_ == 0 {
        let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5865_);
        v___x_5870_ = crate::leanh::lean_box(1);
        v___x_5871_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5871_, 0, v___x_5870_);
        crate::leanh::lean_ctor_set(v___x_5871_, 1, v_a_5867_);
        return v___x_5871_;
    } else {
        let mut v_quotContext_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5879_: u8 = 0;
        let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5872_ = crate::leanh::lean_ctor_get(v_a_5866_, 1);
        v_currMacroScope_5873_ = crate::leanh::lean_ctor_get(v_a_5866_, 2);
        v_ref_5874_ = crate::leanh::lean_ctor_get(v_a_5866_, 5);
        v___x_5875_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5876_ = l_Lean_Syntax_getArg(v_x_5865_, v___x_5875_);
        v___x_5877_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_5878_ = l_Lean_Syntax_getArg(v_x_5865_, v___x_5877_);
        crate::leanh::lean_dec(v_x_5865_);
        v___x_5879_ = 0;
        v___x_5880_ = l_Lean_SourceInfo_fromRef(v_ref_5874_, v___x_5879_);
        v___x_5881_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
        v___x_5883_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_5873_);
        crate::leanh::lean_inc(v_quotContext_5872_);
        v___x_5884_ =
            l_Lean_addMacroScope(v_quotContext_5872_, v___x_5883_, v_currMacroScope_5873_);
        v___x_5885_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8;
        crate::leanh::lean_inc_n(v___x_5880_, 2);
        v___x_5886_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5886_, 0, v___x_5880_);
        crate::leanh::lean_ctor_set(v___x_5886_, 1, v___x_5882_);
        crate::leanh::lean_ctor_set(v___x_5886_, 2, v___x_5884_);
        crate::leanh::lean_ctor_set(v___x_5886_, 3, v___x_5885_);
        v___x_5887_ = l_List_lex___auto__1___closed__9;
        v___x_5888_ = l_Lean_Syntax_node2(v___x_5880_, v___x_5887_, v___x_5876_, v___x_5878_);
        v___x_5889_ = l_Lean_Syntax_node2(v___x_5880_, v___x_5881_, v___x_5886_, v___x_5888_);
        v___x_5890_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5890_, 0, v___x_5889_);
        crate::leanh::lean_ctor_set(v___x_5890_, 1, v_a_5867_);
        return v___x_5890_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(
    mut v_x_5891_: *mut crate::leanh::LeanObject,
    mut v_a_5892_: *mut crate::leanh::LeanObject,
    mut v_a_5893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5894_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(
        v_x_5891_, v_a_5892_, v_a_5893_,
    );
    crate::leanh::lean_dec_ref(v_a_5892_);
    return v_res_5894_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(
    mut v_x_5895_: *mut crate::leanh::LeanObject,
    mut v_a_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    v___x_5898_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    crate::leanh::lean_inc(v_x_5895_);
    v___x_5899_ = l_Lean_Syntax_isOfKind(v_x_5895_, v___x_5898_);
    if v___x_5899_ == 0 {
        let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5895_);
        v___x_5900_ = crate::leanh::lean_box(0);
        v___x_5901_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5901_, 0, v___x_5900_);
        crate::leanh::lean_ctor_set(v___x_5901_, 1, v_a_5897_);
        return v___x_5901_;
    } else {
        let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5905_: u8 = 0;
        v___x_5902_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5903_ = l_Lean_Syntax_getArg(v_x_5895_, v___x_5902_);
        v___x_5904_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        crate::leanh::lean_inc(v___x_5903_);
        v___x_5905_ = l_Lean_Syntax_isOfKind(v___x_5903_, v___x_5904_);
        if v___x_5905_ == 0 {
            let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5903_);
            crate::leanh::lean_dec(v_x_5895_);
            v___x_5906_ = crate::leanh::lean_box(0);
            v___x_5907_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5907_, 0, v___x_5906_);
            crate::leanh::lean_ctor_set(v___x_5907_, 1, v_a_5897_);
            return v___x_5907_;
        } else {
            let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5911_: u8 = 0;
            v___x_5908_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_5909_ = l_Lean_Syntax_getArg(v_x_5895_, v___x_5908_);
            crate::leanh::lean_dec(v_x_5895_);
            v___x_5910_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_5909_);
            v___x_5911_ = l_Lean_Syntax_matchesNull(v___x_5909_, v___x_5910_);
            if v___x_5911_ == 0 {
                let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_5909_);
                crate::leanh::lean_dec(v___x_5903_);
                v___x_5912_ = crate::leanh::lean_box(0);
                v___x_5913_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5913_, 0, v___x_5912_);
                crate::leanh::lean_ctor_set(v___x_5913_, 1, v_a_5897_);
                return v___x_5913_;
            } else {
                let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5917_: u8 = 0;
                let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5914_ = l_Lean_Syntax_getArg(v___x_5909_, v___x_5902_);
                v___x_5915_ = l_Lean_Syntax_getArg(v___x_5909_, v___x_5908_);
                crate::leanh::lean_dec(v___x_5909_);
                v_ref_5916_ = l_Lean_replaceRef(v___x_5903_, v_a_5896_);
                crate::leanh::lean_dec(v___x_5903_);
                v___x_5917_ = 0;
                v___x_5918_ = l_Lean_SourceInfo_fromRef(v_ref_5916_, v___x_5917_);
                crate::leanh::lean_dec(v_ref_5916_);
                v___x_5919_ = l_List_term___x7e___00__closed__1;
                v___x_5920_ = l_List_term___x7e___00__closed__2;
                crate::leanh::lean_inc(v___x_5918_);
                v___x_5921_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5918_);
                crate::leanh::lean_ctor_set(v___x_5921_, 1, v___x_5920_);
                v___x_5922_ = l_Lean_Syntax_node3(
                    v___x_5918_,
                    v___x_5919_,
                    v___x_5914_,
                    v___x_5921_,
                    v___x_5915_,
                );
                v___x_5923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5923_, 0, v___x_5922_);
                crate::leanh::lean_ctor_set(v___x_5923_, 1, v_a_5897_);
                return v___x_5923_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(
    mut v_x_5924_: *mut crate::leanh::LeanObject,
    mut v_a_5925_: *mut crate::leanh::LeanObject,
    mut v_a_5926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5927_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(
        v_x_5924_, v_a_5925_, v_a_5926_,
    );
    crate::leanh::lean_dec(v_a_5925_);
    return v_res_5927_;
}
pub unsafe fn l_List_isPerm___redArg(
    mut v_inst_5928_: *mut crate::leanh::LeanObject,
    mut v_x_5929_: *mut crate::leanh::LeanObject,
    mut v_x_5930_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5931_: u8 = 0;
    let mut v_head_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: u8 = 0;
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5929_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_5928_);
                    v___x_5931_ = l_List_isEmpty___redArg(v_x_5930_);
                    crate::leanh::lean_dec(v_x_5930_);
                    return v___x_5931_;
                } else {
                    v_head_5932_ = crate::leanh::lean_ctor_get(v_x_5929_, 0);
                    crate::leanh::lean_inc_n(v_head_5932_, 2);
                    v_tail_5933_ = crate::leanh::lean_ctor_get(v_x_5929_, 1);
                    crate::leanh::lean_inc(v_tail_5933_);
                    crate::leanh::lean_dec_ref_known(v_x_5929_, 2);
                    crate::leanh::lean_inc(v_x_5930_);
                    crate::leanh::lean_inc_ref(v_inst_5928_);
                    v___x_5934_ = l_List_elem___redArg(v_inst_5928_, v_head_5932_, v_x_5930_);
                    if v___x_5934_ == 0 {
                        crate::leanh::lean_dec(v_tail_5933_);
                        crate::leanh::lean_dec(v_head_5932_);
                        crate::leanh::lean_dec(v_x_5930_);
                        crate::leanh::lean_dec_ref(v_inst_5928_);
                        return v___x_5934_;
                    } else {
                        crate::leanh::lean_inc_ref(v_inst_5928_);
                        v___x_5935_ = l_List_erase___redArg(v_inst_5928_, v_x_5930_, v_head_5932_);
                        v_x_5929_ = v_tail_5933_;
                        v_x_5930_ = v___x_5935_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isPerm___redArg___boxed(
    mut v_inst_5937_: *mut crate::leanh::LeanObject,
    mut v_x_5938_: *mut crate::leanh::LeanObject,
    mut v_x_5939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5940_: u8 = 0;
    let mut v_r_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_List_isPerm___redArg(v_inst_5937_, v_x_5938_, v_x_5939_);
    v_r_5941_ = crate::leanh::lean_box((v_res_5940_) as usize);
    return v_r_5941_;
}
pub unsafe fn l_List_isPerm(
    mut v_00_u03b1_5942_: *mut crate::leanh::LeanObject,
    mut v_inst_5943_: *mut crate::leanh::LeanObject,
    mut v_x_5944_: *mut crate::leanh::LeanObject,
    mut v_x_5945_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5946_: u8 = 0;
    v___x_5946_ = l_List_isPerm___redArg(v_inst_5943_, v_x_5944_, v_x_5945_);
    return v___x_5946_;
}
pub unsafe fn l_List_isPerm___boxed(
    mut v_00_u03b1_5947_: *mut crate::leanh::LeanObject,
    mut v_inst_5948_: *mut crate::leanh::LeanObject,
    mut v_x_5949_: *mut crate::leanh::LeanObject,
    mut v_x_5950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5951_: u8 = 0;
    let mut v_r_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5951_ = l_List_isPerm(v_00_u03b1_5947_, v_inst_5948_, v_x_5949_, v_x_5950_);
    v_r_5952_ = crate::leanh::lean_box((v_res_5951_) as usize);
    return v_r_5952_;
}
pub unsafe fn l_List_any___redArg(
    mut v_x_5953_: *mut crate::leanh::LeanObject,
    mut v_x_5954_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5955_: u8 = 0;
    let mut v_head_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5953_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_5954_);
                    v___x_5955_ = 0;
                    return v___x_5955_;
                } else {
                    v_head_5956_ = crate::leanh::lean_ctor_get(v_x_5953_, 0);
                    crate::leanh::lean_inc(v_head_5956_);
                    v_tail_5957_ = crate::leanh::lean_ctor_get(v_x_5953_, 1);
                    crate::leanh::lean_inc(v_tail_5957_);
                    crate::leanh::lean_dec_ref_known(v_x_5953_, 2);
                    crate::leanh::lean_inc_ref(v_x_5954_);
                    v___x_5958_ = crate::leanh::lean_apply_1(v_x_5954_, v_head_5956_);
                    v___x_5959_ = (crate::leanh::lean_unbox(v___x_5958_) as u8);
                    if v___x_5959_ == 0 {
                        v_x_5953_ = v_tail_5957_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5957_);
                        crate::leanh::lean_dec_ref(v_x_5954_);
                        v___x_5961_ = (crate::leanh::lean_unbox(v___x_5958_) as u8);
                        return v___x_5961_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___redArg___boxed(
    mut v_x_5962_: *mut crate::leanh::LeanObject,
    mut v_x_5963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5964_: u8 = 0;
    let mut v_r_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5964_ = l_List_any___redArg(v_x_5962_, v_x_5963_);
    v_r_5965_ = crate::leanh::lean_box((v_res_5964_) as usize);
    return v_r_5965_;
}
pub unsafe fn l_List_any(
    mut v_00_u03b1_5966_: *mut crate::leanh::LeanObject,
    mut v_x_5967_: *mut crate::leanh::LeanObject,
    mut v_x_5968_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5969_: u8 = 0;
    v___x_5969_ = l_List_any___redArg(v_x_5967_, v_x_5968_);
    return v___x_5969_;
}
pub unsafe fn l_List_any___boxed(
    mut v_00_u03b1_5970_: *mut crate::leanh::LeanObject,
    mut v_x_5971_: *mut crate::leanh::LeanObject,
    mut v_x_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5973_: u8 = 0;
    let mut v_r_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5973_ = l_List_any(v_00_u03b1_5970_, v_x_5971_, v_x_5972_);
    v_r_5974_ = crate::leanh::lean_box((v_res_5973_) as usize);
    return v_r_5974_;
}
pub unsafe fn l_List_all___redArg(
    mut v_x_5975_: *mut crate::leanh::LeanObject,
    mut v_x_5976_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5977_: u8 = 0;
    let mut v_head_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v___x_5982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5975_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_5976_);
                    v___x_5977_ = 1;
                    return v___x_5977_;
                } else {
                    v_head_5978_ = crate::leanh::lean_ctor_get(v_x_5975_, 0);
                    crate::leanh::lean_inc(v_head_5978_);
                    v_tail_5979_ = crate::leanh::lean_ctor_get(v_x_5975_, 1);
                    crate::leanh::lean_inc(v_tail_5979_);
                    crate::leanh::lean_dec_ref_known(v_x_5975_, 2);
                    crate::leanh::lean_inc_ref(v_x_5976_);
                    v___x_5980_ = crate::leanh::lean_apply_1(v_x_5976_, v_head_5978_);
                    v___x_5981_ = (crate::leanh::lean_unbox(v___x_5980_) as u8);
                    if v___x_5981_ == 0 {
                        crate::leanh::lean_dec(v_tail_5979_);
                        crate::leanh::lean_dec_ref(v_x_5976_);
                        v___x_5982_ = (crate::leanh::lean_unbox(v___x_5980_) as u8);
                        return v___x_5982_;
                    } else {
                        v_x_5975_ = v_tail_5979_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___redArg___boxed(
    mut v_x_5984_: *mut crate::leanh::LeanObject,
    mut v_x_5985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5986_: u8 = 0;
    let mut v_r_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5986_ = l_List_all___redArg(v_x_5984_, v_x_5985_);
    v_r_5987_ = crate::leanh::lean_box((v_res_5986_) as usize);
    return v_r_5987_;
}
pub unsafe fn l_List_all(
    mut v_00_u03b1_5988_: *mut crate::leanh::LeanObject,
    mut v_x_5989_: *mut crate::leanh::LeanObject,
    mut v_x_5990_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5991_: u8 = 0;
    v___x_5991_ = l_List_all___redArg(v_x_5989_, v_x_5990_);
    return v___x_5991_;
}
pub unsafe fn l_List_all___boxed(
    mut v_00_u03b1_5992_: *mut crate::leanh::LeanObject,
    mut v_x_5993_: *mut crate::leanh::LeanObject,
    mut v_x_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5995_: u8 = 0;
    let mut v_r_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_List_all(v_00_u03b1_5992_, v_x_5993_, v_x_5994_);
    v_r_5996_ = crate::leanh::lean_box((v_res_5995_) as usize);
    return v_r_5996_;
}
pub unsafe fn l_List_any___at___00List_or_spec__0(
    mut v_x_5997_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5998_: u8 = 0;
    let mut v_head_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: u8 = 0;
    let mut v_tail_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5997_) == 0 {
                    v___x_5998_ = 0;
                    return v___x_5998_;
                } else {
                    v_head_5999_ = crate::leanh::lean_ctor_get(v_x_5997_, 0);
                    v___x_6000_ = (crate::leanh::lean_unbox(v_head_5999_) as u8);
                    if v___x_6000_ == 0 {
                        v_tail_6001_ = crate::leanh::lean_ctor_get(v_x_5997_, 1);
                        v_x_5997_ = v_tail_6001_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6003_ = (crate::leanh::lean_unbox(v_head_5999_) as u8);
                        return v___x_6003_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00List_or_spec__0___boxed(
    mut v_x_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6005_: u8 = 0;
    let mut v_r_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_List_any___at___00List_or_spec__0(v_x_6004_);
    crate::leanh::lean_dec(v_x_6004_);
    v_r_6006_ = crate::leanh::lean_box((v_res_6005_) as usize);
    return v_r_6006_;
}
pub unsafe fn l_List_or(mut v_bs_6007_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_6008_: u8 = 0;
    v___x_6008_ = l_List_any___at___00List_or_spec__0(v_bs_6007_);
    return v___x_6008_;
}
pub unsafe fn l_List_or___boxed(
    mut v_bs_6009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6010_: u8 = 0;
    let mut v_r_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6010_ = l_List_or(v_bs_6009_);
    crate::leanh::lean_dec(v_bs_6009_);
    v_r_6011_ = crate::leanh::lean_box((v_res_6010_) as usize);
    return v_r_6011_;
}
pub unsafe fn l_List_all___at___00List_and_spec__0(
    mut v_x_6012_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6013_: u8 = 0;
    let mut v_head_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: u8 = 0;
    let mut v_tail_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6012_) == 0 {
                    v___x_6013_ = 1;
                    return v___x_6013_;
                } else {
                    v_head_6014_ = crate::leanh::lean_ctor_get(v_x_6012_, 0);
                    v___x_6015_ = (crate::leanh::lean_unbox(v_head_6014_) as u8);
                    if v___x_6015_ == 0 {
                        v___x_6016_ = (crate::leanh::lean_unbox(v_head_6014_) as u8);
                        return v___x_6016_;
                    } else {
                        v_tail_6017_ = crate::leanh::lean_ctor_get(v_x_6012_, 1);
                        v_x_6012_ = v_tail_6017_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00List_and_spec__0___boxed(
    mut v_x_6019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6020_: u8 = 0;
    let mut v_r_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6020_ = l_List_all___at___00List_and_spec__0(v_x_6019_);
    crate::leanh::lean_dec(v_x_6019_);
    v_r_6021_ = crate::leanh::lean_box((v_res_6020_) as usize);
    return v_r_6021_;
}
pub unsafe fn l_List_and(mut v_bs_6022_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_6023_: u8 = 0;
    v___x_6023_ = l_List_all___at___00List_and_spec__0(v_bs_6022_);
    return v___x_6023_;
}
pub unsafe fn l_List_and___boxed(
    mut v_bs_6024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6025_: u8 = 0;
    let mut v_r_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6025_ = l_List_and(v_bs_6024_);
    crate::leanh::lean_dec(v_bs_6024_);
    v_r_6026_ = crate::leanh::lean_box((v_res_6025_) as usize);
    return v_r_6026_;
}
pub unsafe fn l_List_zipWith___redArg(
    mut v_f_6027_: *mut crate::leanh::LeanObject,
    mut v_x_6028_: *mut crate::leanh::LeanObject,
    mut v_x_6029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6038_: u8 = 0;
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6028_) == 0 {
                    crate::leanh::lean_dec(v_x_6029_);
                    crate::leanh::lean_dec(v_f_6027_);
                    v___x_6030_ = crate::leanh::lean_box(0);
                    return v___x_6030_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_6029_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_6028_, 2);
                        crate::leanh::lean_dec(v_f_6027_);
                        v___x_6031_ = crate::leanh::lean_box(0);
                        return v___x_6031_;
                    } else {
                        v_head_6032_ = crate::leanh::lean_ctor_get(v_x_6028_, 0);
                        crate::leanh::lean_inc(v_head_6032_);
                        v_tail_6033_ = crate::leanh::lean_ctor_get(v_x_6028_, 1);
                        crate::leanh::lean_inc(v_tail_6033_);
                        crate::leanh::lean_dec_ref_known(v_x_6028_, 2);
                        v_head_6034_ = crate::leanh::lean_ctor_get(v_x_6029_, 0);
                        v_tail_6035_ = crate::leanh::lean_ctor_get(v_x_6029_, 1);
                        v_isSharedCheck_6044_ = (!crate::leanh::lean_is_exclusive(v_x_6029_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6037_ = v_x_6029_;
                            v_isShared_6038_ = v_isSharedCheck_6044_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_6035_);
                            crate::leanh::lean_inc(v_head_6034_);
                            crate::leanh::lean_dec(v_x_6029_);
                            v___x_6037_ = crate::leanh::lean_box(0);
                            v_isShared_6038_ = v_isSharedCheck_6044_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_6027_);
                v___x_6039_ = crate::leanh::lean_apply_2(v_f_6027_, v_head_6032_, v_head_6034_);
                v___x_6040_ = l_List_zipWith___redArg(v_f_6027_, v_tail_6033_, v_tail_6035_);
                if v_isShared_6038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6037_, 1, v___x_6040_);
                    crate::leanh::lean_ctor_set(v___x_6037_, 0, v___x_6039_);
                    v___x_6042_ = v___x_6037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v___x_6039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 1, v___x_6040_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWith(
    mut v_00_u03b1_6045_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6046_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_6047_: *mut crate::leanh::LeanObject,
    mut v_f_6048_: *mut crate::leanh::LeanObject,
    mut v_x_6049_: *mut crate::leanh::LeanObject,
    mut v_x_6050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6051_ = l_List_zipWith___redArg(v_f_6048_, v_x_6049_, v_x_6050_);
    return v___x_6051_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(
    mut v_x_6052_: *mut crate::leanh::LeanObject,
    mut v_x_6053_: *mut crate::leanh::LeanObject,
    mut v_h__1_6054_: *mut crate::leanh::LeanObject,
    mut v_h__2_6055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6052_) == 0 {
        let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6054_);
        v___x_6056_ = crate::leanh::lean_apply_3(
            v_h__2_6055_,
            v_x_6052_,
            v_x_6053_,
            crate::leanh::lean_box(0),
        );
        return v___x_6056_;
    } else {
        if crate::leanh::lean_obj_tag(v_x_6053_) == 0 {
            let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_6054_);
            v___x_6057_ = crate::leanh::lean_apply_3(
                v_h__2_6055_,
                v_x_6052_,
                v_x_6053_,
                crate::leanh::lean_box(0),
            );
            return v___x_6057_;
        } else {
            let mut v_head_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6055_);
            v_head_6058_ = crate::leanh::lean_ctor_get(v_x_6052_, 0);
            crate::leanh::lean_inc(v_head_6058_);
            v_tail_6059_ = crate::leanh::lean_ctor_get(v_x_6052_, 1);
            crate::leanh::lean_inc(v_tail_6059_);
            crate::leanh::lean_dec_ref_known(v_x_6052_, 2);
            v_head_6060_ = crate::leanh::lean_ctor_get(v_x_6053_, 0);
            crate::leanh::lean_inc(v_head_6060_);
            v_tail_6061_ = crate::leanh::lean_ctor_get(v_x_6053_, 1);
            crate::leanh::lean_inc(v_tail_6061_);
            crate::leanh::lean_dec_ref_known(v_x_6053_, 2);
            v___x_6062_ = crate::leanh::lean_apply_4(
                v_h__1_6054_,
                v_head_6058_,
                v_tail_6059_,
                v_head_6060_,
                v_tail_6061_,
            );
            return v___x_6062_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter(
    mut v_00_u03b1_6063_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6064_: *mut crate::leanh::LeanObject,
    mut v_motive_6065_: *mut crate::leanh::LeanObject,
    mut v_x_6066_: *mut crate::leanh::LeanObject,
    mut v_x_6067_: *mut crate::leanh::LeanObject,
    mut v_h__1_6068_: *mut crate::leanh::LeanObject,
    mut v_h__2_6069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6066_) == 0 {
        let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6068_);
        v___x_6070_ = crate::leanh::lean_apply_3(
            v_h__2_6069_,
            v_x_6066_,
            v_x_6067_,
            crate::leanh::lean_box(0),
        );
        return v___x_6070_;
    } else {
        if crate::leanh::lean_obj_tag(v_x_6067_) == 0 {
            let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_6068_);
            v___x_6071_ = crate::leanh::lean_apply_3(
                v_h__2_6069_,
                v_x_6066_,
                v_x_6067_,
                crate::leanh::lean_box(0),
            );
            return v___x_6071_;
        } else {
            let mut v_head_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_6069_);
            v_head_6072_ = crate::leanh::lean_ctor_get(v_x_6066_, 0);
            crate::leanh::lean_inc(v_head_6072_);
            v_tail_6073_ = crate::leanh::lean_ctor_get(v_x_6066_, 1);
            crate::leanh::lean_inc(v_tail_6073_);
            crate::leanh::lean_dec_ref_known(v_x_6066_, 2);
            v_head_6074_ = crate::leanh::lean_ctor_get(v_x_6067_, 0);
            crate::leanh::lean_inc(v_head_6074_);
            v_tail_6075_ = crate::leanh::lean_ctor_get(v_x_6067_, 1);
            crate::leanh::lean_inc(v_tail_6075_);
            crate::leanh::lean_dec_ref_known(v_x_6067_, 2);
            v___x_6076_ = crate::leanh::lean_apply_4(
                v_h__1_6068_,
                v_head_6072_,
                v_tail_6073_,
                v_head_6074_,
                v_tail_6075_,
            );
            return v___x_6076_;
        }
    }
}
pub unsafe fn l_List_zipWith___at___00List_zip_spec__0___redArg(
    mut v_x_6077_: *mut crate::leanh::LeanObject,
    mut v_x_6078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6085_: u8 = 0;
    let mut v_head_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6090_: u8 = 0;
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6098_: u8 = 0;
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6077_) == 0 {
                    crate::leanh::lean_dec(v_x_6078_);
                    v___x_6079_ = crate::leanh::lean_box(0);
                    return v___x_6079_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_6078_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_6077_, 2);
                        v___x_6080_ = crate::leanh::lean_box(0);
                        return v___x_6080_;
                    } else {
                        v_head_6081_ = crate::leanh::lean_ctor_get(v_x_6077_, 0);
                        v_tail_6082_ = crate::leanh::lean_ctor_get(v_x_6077_, 1);
                        v_isSharedCheck_6099_ = (!crate::leanh::lean_is_exclusive(v_x_6077_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v___x_6084_ = v_x_6077_;
                            v_isShared_6085_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_6082_);
                            crate::leanh::lean_inc(v_head_6081_);
                            crate::leanh::lean_dec(v_x_6077_);
                            v___x_6084_ = crate::leanh::lean_box(0);
                            v_isShared_6085_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_head_6086_ = crate::leanh::lean_ctor_get(v_x_6078_, 0);
                v_tail_6087_ = crate::leanh::lean_ctor_get(v_x_6078_, 1);
                v_isSharedCheck_6098_ = (!crate::leanh::lean_is_exclusive(v_x_6078_)) as u8;
                if v_isSharedCheck_6098_ == 0 {
                    v___x_6089_ = v_x_6078_;
                    v_isShared_6090_ = v_isSharedCheck_6098_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_6087_);
                    crate::leanh::lean_inc(v_head_6086_);
                    crate::leanh::lean_dec(v_x_6078_);
                    v___x_6089_ = crate::leanh::lean_box(0);
                    v_isShared_6090_ = v_isSharedCheck_6098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6085_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6084_, 0);
                    crate::leanh::lean_ctor_set(v___x_6084_, 1, v_head_6086_);
                    v___x_6092_ = v___x_6084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_head_6081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6097_, 1, v_head_6086_);
                    v___x_6092_ = v_reuseFailAlloc_6097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6093_ =
                    l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_6082_, v_tail_6087_);
                if v_isShared_6090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6089_, 1, v___x_6093_);
                    crate::leanh::lean_ctor_set(v___x_6089_, 0, v___x_6092_);
                    v___x_6095_ = v___x_6089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6096_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6096_, 1, v___x_6093_);
                    v___x_6095_ = v_reuseFailAlloc_6096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zip___redArg(
    mut v_xs_6100_: *mut crate::leanh::LeanObject,
    mut v_ys_6101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6102_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_6100_, v_ys_6101_);
    return v___x_6102_;
}
pub unsafe fn l_List_zip(
    mut v_00_u03b1_6103_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6104_: *mut crate::leanh::LeanObject,
    mut v_xs_6105_: *mut crate::leanh::LeanObject,
    mut v_ys_6106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_6105_, v_ys_6106_);
    return v___x_6107_;
}
pub unsafe fn l_List_zipWith___at___00List_zip_spec__0(
    mut v_00_u03b1_6108_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6109_: *mut crate::leanh::LeanObject,
    mut v_x_6110_: *mut crate::leanh::LeanObject,
    mut v_x_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6112_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_6110_, v_x_6111_);
    return v___x_6112_;
}
pub unsafe fn l_List_zipWithAll___redArg___lam__0(
    mut v_f_6113_: *mut crate::leanh::LeanObject,
    mut v_b_6114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6115_ = crate::leanh::lean_box(0);
    v___x_6116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6116_, 0, v_b_6114_);
    v___x_6117_ = crate::leanh::lean_apply_2(v_f_6113_, v___x_6115_, v___x_6116_);
    return v___x_6117_;
}
pub unsafe fn l_List_zipWithAll___redArg___lam__1(
    mut v_f_6118_: *mut crate::leanh::LeanObject,
    mut v_a_6119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6120_, 0, v_a_6119_);
    v___x_6121_ = crate::leanh::lean_box(0);
    v___x_6122_ = crate::leanh::lean_apply_2(v_f_6118_, v___x_6120_, v___x_6121_);
    return v___x_6122_;
}
pub unsafe fn l_List_zipWithAll___redArg(
    mut v_f_6123_: *mut crate::leanh::LeanObject,
    mut v_x_6124_: *mut crate::leanh::LeanObject,
    mut v_x_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6136_: u8 = 0;
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6124_) == 0 {
                    v___f_6126_ = crate::leanh::lean_alloc_closure(
                        l_List_zipWithAll___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_6126_, 0, v_f_6123_);
                    v___x_6127_ = l_List_map___redArg(v___f_6126_, v_x_6125_);
                    return v___x_6127_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_6125_) == 0 {
                        v___f_6128_ = crate::leanh::lean_alloc_closure(
                            l_List_zipWithAll___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_6128_, 0, v_f_6123_);
                        v___x_6129_ = l_List_map___redArg(v___f_6128_, v_x_6124_);
                        return v___x_6129_;
                    } else {
                        v_head_6130_ = crate::leanh::lean_ctor_get(v_x_6124_, 0);
                        crate::leanh::lean_inc(v_head_6130_);
                        v_tail_6131_ = crate::leanh::lean_ctor_get(v_x_6124_, 1);
                        crate::leanh::lean_inc(v_tail_6131_);
                        crate::leanh::lean_dec_ref_known(v_x_6124_, 2);
                        v_head_6132_ = crate::leanh::lean_ctor_get(v_x_6125_, 0);
                        v_tail_6133_ = crate::leanh::lean_ctor_get(v_x_6125_, 1);
                        v_isSharedCheck_6144_ = (!crate::leanh::lean_is_exclusive(v_x_6125_)) as u8;
                        if v_isSharedCheck_6144_ == 0 {
                            v___x_6135_ = v_x_6125_;
                            v_isShared_6136_ = v_isSharedCheck_6144_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_6133_);
                            crate::leanh::lean_inc(v_head_6132_);
                            crate::leanh::lean_dec(v_x_6125_);
                            v___x_6135_ = crate::leanh::lean_box(0);
                            v_isShared_6136_ = v_isSharedCheck_6144_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6137_, 0, v_head_6130_);
                v___x_6138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6138_, 0, v_head_6132_);
                crate::leanh::lean_inc(v_f_6123_);
                v___x_6139_ = crate::leanh::lean_apply_2(v_f_6123_, v___x_6137_, v___x_6138_);
                v___x_6140_ = l_List_zipWithAll___redArg(v_f_6123_, v_tail_6131_, v_tail_6133_);
                if v_isShared_6136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6135_, 1, v___x_6140_);
                    crate::leanh::lean_ctor_set(v___x_6135_, 0, v___x_6139_);
                    v___x_6142_ = v___x_6135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6143_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 0, v___x_6139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 1, v___x_6140_);
                    v___x_6142_ = v_reuseFailAlloc_6143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithAll(
    mut v_00_u03b1_6145_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6146_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_6147_: *mut crate::leanh::LeanObject,
    mut v_f_6148_: *mut crate::leanh::LeanObject,
    mut v_x_6149_: *mut crate::leanh::LeanObject,
    mut v_x_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6151_ = l_List_zipWithAll___redArg(v_f_6148_, v_x_6149_, v_x_6150_);
    return v___x_6151_;
}
pub unsafe fn l_List_unzip___redArg(
    mut v_x_6152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6158_: u8 = 0;
    let mut v_fst_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6169_: u8 = 0;
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6179_: u8 = 0;
    let mut v_isSharedCheck_6180_: u8 = 0;
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6152_) == 0 {
                    v___x_6153_ = l_List_partition___redArg___closed__0;
                    return v___x_6153_;
                } else {
                    v_head_6154_ = crate::leanh::lean_ctor_get(v_x_6152_, 0);
                    v_tail_6155_ = crate::leanh::lean_ctor_get(v_x_6152_, 1);
                    v_isSharedCheck_6181_ = (!crate::leanh::lean_is_exclusive(v_x_6152_)) as u8;
                    if v_isSharedCheck_6181_ == 0 {
                        v___x_6157_ = v_x_6152_;
                        v_isShared_6158_ = v_isSharedCheck_6181_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6155_);
                        crate::leanh::lean_inc(v_head_6154_);
                        crate::leanh::lean_dec(v_x_6152_);
                        v___x_6157_ = crate::leanh::lean_box(0);
                        v_isShared_6158_ = v_isSharedCheck_6181_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6159_ = crate::leanh::lean_ctor_get(v_head_6154_, 0);
                v_snd_6160_ = crate::leanh::lean_ctor_get(v_head_6154_, 1);
                v_isSharedCheck_6180_ = (!crate::leanh::lean_is_exclusive(v_head_6154_)) as u8;
                if v_isSharedCheck_6180_ == 0 {
                    v___x_6162_ = v_head_6154_;
                    v_isShared_6163_ = v_isSharedCheck_6180_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6160_);
                    crate::leanh::lean_inc(v_fst_6159_);
                    crate::leanh::lean_dec(v_head_6154_);
                    v___x_6162_ = crate::leanh::lean_box(0);
                    v_isShared_6163_ = v_isSharedCheck_6180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6164_ = l_List_unzip___redArg(v_tail_6155_);
                v_fst_6165_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                v_snd_6166_ = crate::leanh::lean_ctor_get(v___x_6164_, 1);
                v_isSharedCheck_6179_ = (!crate::leanh::lean_is_exclusive(v___x_6164_)) as u8;
                if v_isSharedCheck_6179_ == 0 {
                    v___x_6168_ = v___x_6164_;
                    v_isShared_6169_ = v_isSharedCheck_6179_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6166_);
                    crate::leanh::lean_inc(v_fst_6165_);
                    crate::leanh::lean_dec(v___x_6164_);
                    v___x_6168_ = crate::leanh::lean_box(0);
                    v_isShared_6169_ = v_isSharedCheck_6179_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6157_, 1, v_fst_6165_);
                    crate::leanh::lean_ctor_set(v___x_6157_, 0, v_fst_6159_);
                    v___x_6171_ = v___x_6157_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6178_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_fst_6159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6178_, 1, v_fst_6165_);
                    v___x_6171_ = v_reuseFailAlloc_6178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6163_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6162_, 1);
                    crate::leanh::lean_ctor_set(v___x_6162_, 1, v_snd_6166_);
                    crate::leanh::lean_ctor_set(v___x_6162_, 0, v_snd_6160_);
                    v___x_6173_ = v___x_6162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6177_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_snd_6160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6177_, 1, v_snd_6166_);
                    v___x_6173_ = v_reuseFailAlloc_6177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6168_, 1, v___x_6173_);
                    crate::leanh::lean_ctor_set(v___x_6168_, 0, v___x_6171_);
                    v___x_6175_ = v___x_6168_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 0, v___x_6171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 1, v___x_6173_);
                    v___x_6175_ = v_reuseFailAlloc_6176_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_unzip(
    mut v_00_u03b1_6182_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6183_: *mut crate::leanh::LeanObject,
    mut v_x_6184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6185_ = l_List_unzip___redArg(v_x_6184_);
    return v___x_6185_;
}
pub unsafe fn l_List_sum___redArg___lam__0(
    mut v_inst_6186_: *mut crate::leanh::LeanObject,
    mut v_x1_6187_: *mut crate::leanh::LeanObject,
    mut v_x2_6188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6189_ = crate::leanh::lean_apply_2(v_inst_6186_, v_x1_6187_, v_x2_6188_);
    return v___x_6189_;
}
pub unsafe fn l_List_sum___redArg(
    mut v_inst_6190_: *mut crate::leanh::LeanObject,
    mut v_inst_6191_: *mut crate::leanh::LeanObject,
    mut v_l_6192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6193_ = crate::leanh::lean_alloc_closure(
        l_List_sum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6193_, 0, v_inst_6190_);
    v___x_6194_ = l_List_foldr___redArg(v___f_6193_, v_inst_6191_, v_l_6192_);
    return v___x_6194_;
}
pub unsafe fn l_List_sum___redArg___boxed(
    mut v_inst_6195_: *mut crate::leanh::LeanObject,
    mut v_inst_6196_: *mut crate::leanh::LeanObject,
    mut v_l_6197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6198_ = l_List_sum___redArg(v_inst_6195_, v_inst_6196_, v_l_6197_);
    crate::leanh::lean_dec(v_inst_6196_);
    return v_res_6198_;
}
pub unsafe fn l_List_sum(
    mut v_00_u03b1_6199_: *mut crate::leanh::LeanObject,
    mut v_inst_6200_: *mut crate::leanh::LeanObject,
    mut v_inst_6201_: *mut crate::leanh::LeanObject,
    mut v_l_6202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6203_ = l_List_sum___redArg(v_inst_6200_, v_inst_6201_, v_l_6202_);
    return v___x_6203_;
}
pub unsafe fn l_List_sum___boxed(
    mut v_00_u03b1_6204_: *mut crate::leanh::LeanObject,
    mut v_inst_6205_: *mut crate::leanh::LeanObject,
    mut v_inst_6206_: *mut crate::leanh::LeanObject,
    mut v_l_6207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6208_ = l_List_sum(v_00_u03b1_6204_, v_inst_6205_, v_inst_6206_, v_l_6207_);
    crate::leanh::lean_dec(v_inst_6206_);
    return v_res_6208_;
}
pub unsafe fn l_List_prod___redArg(
    mut v_inst_6209_: *mut crate::leanh::LeanObject,
    mut v_inst_6210_: *mut crate::leanh::LeanObject,
    mut v_l_6211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6212_ = crate::leanh::lean_alloc_closure(
        l_List_sum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6212_, 0, v_inst_6209_);
    v___x_6213_ = l_List_foldr___redArg(v___f_6212_, v_inst_6210_, v_l_6211_);
    return v___x_6213_;
}
pub unsafe fn l_List_prod___redArg___boxed(
    mut v_inst_6214_: *mut crate::leanh::LeanObject,
    mut v_inst_6215_: *mut crate::leanh::LeanObject,
    mut v_l_6216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6217_ = l_List_prod___redArg(v_inst_6214_, v_inst_6215_, v_l_6216_);
    crate::leanh::lean_dec(v_inst_6215_);
    return v_res_6217_;
}
pub unsafe fn l_List_prod(
    mut v_00_u03b1_6218_: *mut crate::leanh::LeanObject,
    mut v_inst_6219_: *mut crate::leanh::LeanObject,
    mut v_inst_6220_: *mut crate::leanh::LeanObject,
    mut v_l_6221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6222_ = l_List_prod___redArg(v_inst_6219_, v_inst_6220_, v_l_6221_);
    return v___x_6222_;
}
pub unsafe fn l_List_prod___boxed(
    mut v_00_u03b1_6223_: *mut crate::leanh::LeanObject,
    mut v_inst_6224_: *mut crate::leanh::LeanObject,
    mut v_inst_6225_: *mut crate::leanh::LeanObject,
    mut v_l_6226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6227_ = l_List_prod(v_00_u03b1_6223_, v_inst_6224_, v_inst_6225_, v_l_6226_);
    crate::leanh::lean_dec(v_inst_6225_);
    return v_res_6227_;
}
pub unsafe fn l_List_range_loop(
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_a_6229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6231_: u8 = 0;
    let mut v_one_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6230_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_6231_ = lean_nat_dec_eq(v_a_6228_, v_zero_6230_);
                if v_isZero_6231_ == 1 {
                    crate::leanh::lean_dec(v_a_6228_);
                    return v_a_6229_;
                } else {
                    v_one_6232_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_6233_ = lean_nat_sub(v_a_6228_, v_one_6232_);
                    crate::leanh::lean_dec(v_a_6228_);
                    crate::leanh::lean_inc(v_n_6233_);
                    v___x_6234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6234_, 0, v_n_6233_);
                    crate::leanh::lean_ctor_set(v___x_6234_, 1, v_a_6229_);
                    v_a_6228_ = v_n_6233_;
                    v_a_6229_ = v___x_6234_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_range(
    mut v_n_6236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6237_ = crate::leanh::lean_box(0);
    v___x_6238_ = l_List_range_loop(v_n_6236_, v___x_6237_);
    return v___x_6238_;
}
pub unsafe fn l_List_range_x27(
    mut v_x_6239_: *mut crate::leanh::LeanObject,
    mut v_x_6240_: *mut crate::leanh::LeanObject,
    mut v_x_6241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6243_: u8 = 0;
    v_zero_6242_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6243_ = lean_nat_dec_eq(v_x_6240_, v_zero_6242_);
    if v_isZero_6243_ == 1 {
        let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6239_);
        v___x_6244_ = crate::leanh::lean_box(0);
        return v___x_6244_;
    } else {
        let mut v_one_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_6245_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6246_ = lean_nat_sub(v_x_6240_, v_one_6245_);
        v___x_6247_ = lean_nat_add(v_x_6239_, v_x_6241_);
        v___x_6248_ = l_List_range_x27(v___x_6247_, v_n_6246_, v_x_6241_);
        crate::leanh::lean_dec(v_n_6246_);
        v___x_6249_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6249_, 0, v_x_6239_);
        crate::leanh::lean_ctor_set(v___x_6249_, 1, v___x_6248_);
        return v___x_6249_;
    }
}
pub unsafe fn l_List_range_x27___boxed(
    mut v_x_6250_: *mut crate::leanh::LeanObject,
    mut v_x_6251_: *mut crate::leanh::LeanObject,
    mut v_x_6252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6253_ = l_List_range_x27(v_x_6250_, v_x_6251_, v_x_6252_);
    crate::leanh::lean_dec(v_x_6252_);
    crate::leanh::lean_dec(v_x_6251_);
    return v_res_6253_;
}
pub unsafe fn l_List_zipIdx___redArg(
    mut v_x_6254_: *mut crate::leanh::LeanObject,
    mut v_x_6255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6261_: u8 = 0;
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6254_) == 0 {
                    crate::leanh::lean_dec(v_x_6255_);
                    v___x_6256_ = crate::leanh::lean_box(0);
                    return v___x_6256_;
                } else {
                    v_head_6257_ = crate::leanh::lean_ctor_get(v_x_6254_, 0);
                    v_tail_6258_ = crate::leanh::lean_ctor_get(v_x_6254_, 1);
                    v_isSharedCheck_6269_ = (!crate::leanh::lean_is_exclusive(v_x_6254_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6260_ = v_x_6254_;
                        v_isShared_6261_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6258_);
                        crate::leanh::lean_inc(v_head_6257_);
                        crate::leanh::lean_dec(v_x_6254_);
                        v___x_6260_ = crate::leanh::lean_box(0);
                        v_isShared_6261_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_6255_);
                v___x_6262_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6262_, 0, v_head_6257_);
                crate::leanh::lean_ctor_set(v___x_6262_, 1, v_x_6255_);
                v___x_6263_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6264_ = lean_nat_add(v_x_6255_, v___x_6263_);
                crate::leanh::lean_dec(v_x_6255_);
                v___x_6265_ = l_List_zipIdx___redArg(v_tail_6258_, v___x_6264_);
                if v_isShared_6261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6260_, 1, v___x_6265_);
                    crate::leanh::lean_ctor_set(v___x_6260_, 0, v___x_6262_);
                    v___x_6267_ = v___x_6260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 1, v___x_6265_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipIdx(
    mut v_00_u03b1_6270_: *mut crate::leanh::LeanObject,
    mut v_x_6271_: *mut crate::leanh::LeanObject,
    mut v_x_6272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6273_ = l_List_zipIdx___redArg(v_x_6271_, v_x_6272_);
    return v___x_6273_;
}
pub unsafe fn l_List_min_x3f___redArg(
    mut v_inst_6274_: *mut crate::leanh::LeanObject,
    mut v_x_6275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6275_) == 0 {
        let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_6274_);
        v___x_6276_ = crate::leanh::lean_box(0);
        return v___x_6276_;
    } else {
        let mut v_head_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_6277_ = crate::leanh::lean_ctor_get(v_x_6275_, 0);
        crate::leanh::lean_inc(v_head_6277_);
        v_tail_6278_ = crate::leanh::lean_ctor_get(v_x_6275_, 1);
        crate::leanh::lean_inc(v_tail_6278_);
        crate::leanh::lean_dec_ref_known(v_x_6275_, 2);
        v___x_6279_ = l_List_foldl___redArg(v_inst_6274_, v_head_6277_, v_tail_6278_);
        v___x_6280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6280_, 0, v___x_6279_);
        return v___x_6280_;
    }
}
pub unsafe fn l_List_min_x3f(
    mut v_00_u03b1_6281_: *mut crate::leanh::LeanObject,
    mut v_inst_6282_: *mut crate::leanh::LeanObject,
    mut v_x_6283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6284_ = l_List_min_x3f___redArg(v_inst_6282_, v_x_6283_);
    return v___x_6284_;
}
pub unsafe fn l_List_min___redArg(
    mut v_inst_6285_: *mut crate::leanh::LeanObject,
    mut v_x_6286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_6287_ = crate::leanh::lean_ctor_get(v_x_6286_, 0);
    crate::leanh::lean_inc(v_head_6287_);
    v_tail_6288_ = crate::leanh::lean_ctor_get(v_x_6286_, 1);
    crate::leanh::lean_inc(v_tail_6288_);
    crate::leanh::lean_dec(v_x_6286_);
    v___x_6289_ = l_List_foldl___redArg(v_inst_6285_, v_head_6287_, v_tail_6288_);
    return v___x_6289_;
}
pub unsafe fn l_List_min(
    mut v_00_u03b1_6290_: *mut crate::leanh::LeanObject,
    mut v_inst_6291_: *mut crate::leanh::LeanObject,
    mut v_x_6292_: *mut crate::leanh::LeanObject,
    mut v_x_6293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6294_ = l_List_min___redArg(v_inst_6291_, v_x_6292_);
    return v___x_6294_;
}
pub unsafe fn l_List_max_x3f___redArg(
    mut v_inst_6295_: *mut crate::leanh::LeanObject,
    mut v_x_6296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6296_) == 0 {
        let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_6295_);
        v___x_6297_ = crate::leanh::lean_box(0);
        return v___x_6297_;
    } else {
        let mut v_head_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_6298_ = crate::leanh::lean_ctor_get(v_x_6296_, 0);
        crate::leanh::lean_inc(v_head_6298_);
        v_tail_6299_ = crate::leanh::lean_ctor_get(v_x_6296_, 1);
        crate::leanh::lean_inc(v_tail_6299_);
        crate::leanh::lean_dec_ref_known(v_x_6296_, 2);
        v___x_6300_ = l_List_foldl___redArg(v_inst_6295_, v_head_6298_, v_tail_6299_);
        v___x_6301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6301_, 0, v___x_6300_);
        return v___x_6301_;
    }
}
pub unsafe fn l_List_max_x3f(
    mut v_00_u03b1_6302_: *mut crate::leanh::LeanObject,
    mut v_inst_6303_: *mut crate::leanh::LeanObject,
    mut v_x_6304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6305_ = l_List_max_x3f___redArg(v_inst_6303_, v_x_6304_);
    return v___x_6305_;
}
pub unsafe fn l_List_max___redArg(
    mut v_inst_6306_: *mut crate::leanh::LeanObject,
    mut v_x_6307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_6308_ = crate::leanh::lean_ctor_get(v_x_6307_, 0);
    crate::leanh::lean_inc(v_head_6308_);
    v_tail_6309_ = crate::leanh::lean_ctor_get(v_x_6307_, 1);
    crate::leanh::lean_inc(v_tail_6309_);
    crate::leanh::lean_dec(v_x_6307_);
    v___x_6310_ = l_List_foldl___redArg(v_inst_6306_, v_head_6308_, v_tail_6309_);
    return v___x_6310_;
}
pub unsafe fn l_List_max(
    mut v_00_u03b1_6311_: *mut crate::leanh::LeanObject,
    mut v_inst_6312_: *mut crate::leanh::LeanObject,
    mut v_x_6313_: *mut crate::leanh::LeanObject,
    mut v_x_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6315_ = l_List_max___redArg(v_inst_6312_, v_x_6313_);
    return v___x_6315_;
}
pub unsafe fn l_List_intersperse___redArg(
    mut v_sep_6316_: *mut crate::leanh::LeanObject,
    mut v_x_6317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6328_: u8 = 0;
    let mut v_unused_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6317_) == 0 {
                    crate::leanh::lean_dec(v_sep_6316_);
                    return v_x_6317_;
                } else {
                    v_tail_6318_ = crate::leanh::lean_ctor_get(v_x_6317_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_6318_) == 0 {
                        crate::leanh::lean_dec(v_sep_6316_);
                        return v_x_6317_;
                    } else {
                        crate::leanh::lean_inc_ref(v_tail_6318_);
                        v_head_6319_ = crate::leanh::lean_ctor_get(v_x_6317_, 0);
                        v_isSharedCheck_6328_ = (!crate::leanh::lean_is_exclusive(v_x_6317_)) as u8;
                        if v_isSharedCheck_6328_ == 0 {
                            v_unused_6329_ = crate::leanh::lean_ctor_get(v_x_6317_, 1);
                            crate::leanh::lean_dec(v_unused_6329_);
                            v___x_6321_ = v_x_6317_;
                            v_isShared_6322_ = v_isSharedCheck_6328_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_6319_);
                            crate::leanh::lean_dec(v_x_6317_);
                            v___x_6321_ = crate::leanh::lean_box(0);
                            v_isShared_6322_ = v_isSharedCheck_6328_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_sep_6316_);
                v___x_6323_ = l_List_intersperse___redArg(v_sep_6316_, v_tail_6318_);
                if v_isShared_6322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6321_, 1, v___x_6323_);
                    crate::leanh::lean_ctor_set(v___x_6321_, 0, v_sep_6316_);
                    v___x_6325_ = v___x_6321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6327_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_sep_6316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 1, v___x_6323_);
                    v___x_6325_ = v_reuseFailAlloc_6327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6326_, 0, v_head_6319_);
                crate::leanh::lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                return v___x_6326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_intersperse(
    mut v_00_u03b1_6330_: *mut crate::leanh::LeanObject,
    mut v_sep_6331_: *mut crate::leanh::LeanObject,
    mut v_x_6332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6333_ = l_List_intersperse___redArg(v_sep_6331_, v_x_6332_);
    return v___x_6333_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(
    mut v___x_6334_: *mut crate::leanh::LeanObject,
    mut v_x_6335_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6336_: u8 = 0;
    let mut v_head_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: u8 = 0;
    let mut v___x_6342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6335_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_6334_);
                    v___x_6336_ = 0;
                    return v___x_6336_;
                } else {
                    v_head_6337_ = crate::leanh::lean_ctor_get(v_x_6335_, 0);
                    crate::leanh::lean_inc(v_head_6337_);
                    v_tail_6338_ = crate::leanh::lean_ctor_get(v_x_6335_, 1);
                    crate::leanh::lean_inc(v_tail_6338_);
                    crate::leanh::lean_dec_ref_known(v_x_6335_, 2);
                    crate::leanh::lean_inc_ref(v___x_6334_);
                    v___x_6339_ = crate::leanh::lean_apply_1(v___x_6334_, v_head_6337_);
                    v___x_6340_ = (crate::leanh::lean_unbox(v___x_6339_) as u8);
                    if v___x_6340_ == 0 {
                        v_x_6335_ = v_tail_6338_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_6338_);
                        crate::leanh::lean_dec_ref(v___x_6334_);
                        v___x_6342_ = (crate::leanh::lean_unbox(v___x_6339_) as u8);
                        return v___x_6342_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(
    mut v___x_6343_: *mut crate::leanh::LeanObject,
    mut v_x_6344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6345_: u8 = 0;
    let mut v_r_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6345_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_6343_, v_x_6344_);
    v_r_6346_ = crate::leanh::lean_box((v_res_6345_) as usize);
    return v_r_6346_;
}
pub unsafe fn l_List_eraseDupsBy_loop___redArg(
    mut v_r_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6355_: u8 = 0;
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: u8 = 0;
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6348_) == 0 {
                    crate::leanh::lean_dec_ref(v_r_6347_);
                    v___x_6350_ = l_List_reverse___redArg(v_a_6349_);
                    return v___x_6350_;
                } else {
                    v_head_6351_ = crate::leanh::lean_ctor_get(v_a_6348_, 0);
                    v_tail_6352_ = crate::leanh::lean_ctor_get(v_a_6348_, 1);
                    v_isSharedCheck_6363_ = (!crate::leanh::lean_is_exclusive(v_a_6348_)) as u8;
                    if v_isSharedCheck_6363_ == 0 {
                        v___x_6354_ = v_a_6348_;
                        v_isShared_6355_ = v_isSharedCheck_6363_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6352_);
                        crate::leanh::lean_inc(v_head_6351_);
                        crate::leanh::lean_dec(v_a_6348_);
                        v___x_6354_ = crate::leanh::lean_box(0);
                        v_isShared_6355_ = v_isSharedCheck_6363_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_r_6347_);
                crate::leanh::lean_inc(v_head_6351_);
                v___x_6356_ = crate::leanh::lean_apply_1(v_r_6347_, v_head_6351_);
                crate::leanh::lean_inc(v_a_6349_);
                v___x_6357_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(
                    v___x_6356_,
                    v_a_6349_,
                );
                if v___x_6357_ == 0 {
                    if v_isShared_6355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6354_, 1, v_a_6349_);
                        v___x_6359_ = v___x_6354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6361_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_head_6351_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 1, v_a_6349_);
                        v___x_6359_ = v_reuseFailAlloc_6361_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6354_);
                    crate::leanh::lean_dec(v_head_6351_);
                    v_a_6348_ = v_tail_6352_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_6348_ = v_tail_6352_;
                v_a_6349_ = v___x_6359_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_eraseDupsBy_loop(
    mut v_00_u03b1_6364_: *mut crate::leanh::LeanObject,
    mut v_r_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6368_ = l_List_eraseDupsBy_loop___redArg(v_r_6365_, v_a_6366_, v_a_6367_);
    return v___x_6368_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0(
    mut v_00_u03b1_6369_: *mut crate::leanh::LeanObject,
    mut v___x_6370_: *mut crate::leanh::LeanObject,
    mut v_x_6371_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6372_: u8 = 0;
    v___x_6372_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_6370_, v_x_6371_);
    return v___x_6372_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(
    mut v_00_u03b1_6373_: *mut crate::leanh::LeanObject,
    mut v___x_6374_: *mut crate::leanh::LeanObject,
    mut v_x_6375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6376_: u8 = 0;
    let mut v_r_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6376_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_6373_, v___x_6374_, v_x_6375_);
    v_r_6377_ = crate::leanh::lean_box((v_res_6376_) as usize);
    return v_r_6377_;
}
pub unsafe fn l_List_eraseDupsBy___redArg(
    mut v_r_6378_: *mut crate::leanh::LeanObject,
    mut v_as_6379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6380_ = crate::leanh::lean_box(0);
    v___x_6381_ = l_List_eraseDupsBy_loop___redArg(v_r_6378_, v_as_6379_, v___x_6380_);
    return v___x_6381_;
}
pub unsafe fn l_List_eraseDupsBy(
    mut v_00_u03b1_6382_: *mut crate::leanh::LeanObject,
    mut v_r_6383_: *mut crate::leanh::LeanObject,
    mut v_as_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6385_ = l_List_eraseDupsBy___redArg(v_r_6383_, v_as_6384_);
    return v___x_6385_;
}
pub unsafe fn l_List_eraseDups___redArg___lam__0(
    mut v_inst_6386_: *mut crate::leanh::LeanObject,
    mut v_x1_6387_: *mut crate::leanh::LeanObject,
    mut v_x2_6388_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: u8 = 0;
    v___x_6389_ = crate::leanh::lean_apply_2(v_inst_6386_, v_x1_6387_, v_x2_6388_);
    v___x_6390_ = (crate::leanh::lean_unbox(v___x_6389_) as u8);
    return v___x_6390_;
}
pub unsafe fn l_List_eraseDups___redArg___lam__0___boxed(
    mut v_inst_6391_: *mut crate::leanh::LeanObject,
    mut v_x1_6392_: *mut crate::leanh::LeanObject,
    mut v_x2_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6394_: u8 = 0;
    let mut v_r_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_List_eraseDups___redArg___lam__0(v_inst_6391_, v_x1_6392_, v_x2_6393_);
    v_r_6395_ = crate::leanh::lean_box((v_res_6394_) as usize);
    return v_r_6395_;
}
pub unsafe fn l_List_eraseDups___redArg(
    mut v_inst_6396_: *mut crate::leanh::LeanObject,
    mut v_as_6397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6398_ = crate::leanh::lean_alloc_closure(
        l_List_eraseDups___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6398_, 0, v_inst_6396_);
    v___x_6399_ = l_List_eraseDupsBy___redArg(v___f_6398_, v_as_6397_);
    return v___x_6399_;
}
pub unsafe fn l_List_eraseDups(
    mut v_00_u03b1_6400_: *mut crate::leanh::LeanObject,
    mut v_inst_6401_: *mut crate::leanh::LeanObject,
    mut v_as_6402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6403_ = l_List_eraseDups___redArg(v_inst_6401_, v_as_6402_);
    return v___x_6403_;
}
pub unsafe fn l_List_eraseRepsBy_loop___redArg(
    mut v_r_6404_: *mut crate::leanh::LeanObject,
    mut v_a_6405_: *mut crate::leanh::LeanObject,
    mut v_a_6406_: *mut crate::leanh::LeanObject,
    mut v_a_6407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: u8 = 0;
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6406_) == 0 {
                    crate::leanh::lean_dec_ref(v_r_6404_);
                    v___x_6408_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6408_, 0, v_a_6405_);
                    crate::leanh::lean_ctor_set(v___x_6408_, 1, v_a_6407_);
                    v___x_6409_ = l_List_reverse___redArg(v___x_6408_);
                    return v___x_6409_;
                } else {
                    v_head_6410_ = crate::leanh::lean_ctor_get(v_a_6406_, 0);
                    v_tail_6411_ = crate::leanh::lean_ctor_get(v_a_6406_, 1);
                    v_isSharedCheck_6422_ = (!crate::leanh::lean_is_exclusive(v_a_6406_)) as u8;
                    if v_isSharedCheck_6422_ == 0 {
                        v___x_6413_ = v_a_6406_;
                        v_isShared_6414_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6411_);
                        crate::leanh::lean_inc(v_head_6410_);
                        crate::leanh::lean_dec(v_a_6406_);
                        v___x_6413_ = crate::leanh::lean_box(0);
                        v_isShared_6414_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_r_6404_);
                crate::leanh::lean_inc(v_head_6410_);
                crate::leanh::lean_inc(v_a_6405_);
                v___x_6415_ = crate::leanh::lean_apply_2(v_r_6404_, v_a_6405_, v_head_6410_);
                v___x_6416_ = (crate::leanh::lean_unbox(v___x_6415_) as u8);
                if v___x_6416_ == 0 {
                    if v_isShared_6414_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6413_, 1, v_a_6407_);
                        crate::leanh::lean_ctor_set(v___x_6413_, 0, v_a_6405_);
                        v___x_6418_ = v___x_6413_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6420_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6405_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 1, v_a_6407_);
                        v___x_6418_ = v_reuseFailAlloc_6420_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6413_);
                    crate::leanh::lean_dec(v_head_6410_);
                    v_a_6406_ = v_tail_6411_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_6405_ = v_head_6410_;
                v_a_6406_ = v_tail_6411_;
                v_a_6407_ = v___x_6418_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_eraseRepsBy_loop(
    mut v_00_u03b1_6423_: *mut crate::leanh::LeanObject,
    mut v_r_6424_: *mut crate::leanh::LeanObject,
    mut v_a_6425_: *mut crate::leanh::LeanObject,
    mut v_a_6426_: *mut crate::leanh::LeanObject,
    mut v_a_6427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l_List_eraseRepsBy_loop___redArg(v_r_6424_, v_a_6425_, v_a_6426_, v_a_6427_);
    return v___x_6428_;
}
pub unsafe fn l_List_eraseRepsBy___redArg(
    mut v_r_6429_: *mut crate::leanh::LeanObject,
    mut v_x_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6430_) == 0 {
        crate::leanh::lean_dec_ref(v_r_6429_);
        return v_x_6430_;
    } else {
        let mut v_head_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_6431_ = crate::leanh::lean_ctor_get(v_x_6430_, 0);
        crate::leanh::lean_inc(v_head_6431_);
        v_tail_6432_ = crate::leanh::lean_ctor_get(v_x_6430_, 1);
        crate::leanh::lean_inc(v_tail_6432_);
        crate::leanh::lean_dec_ref_known(v_x_6430_, 2);
        v___x_6433_ = crate::leanh::lean_box(0);
        v___x_6434_ =
            l_List_eraseRepsBy_loop___redArg(v_r_6429_, v_head_6431_, v_tail_6432_, v___x_6433_);
        return v___x_6434_;
    }
}
pub unsafe fn l_List_eraseRepsBy(
    mut v_00_u03b1_6435_: *mut crate::leanh::LeanObject,
    mut v_r_6436_: *mut crate::leanh::LeanObject,
    mut v_x_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6438_ = l_List_eraseRepsBy___redArg(v_r_6436_, v_x_6437_);
    return v___x_6438_;
}
pub unsafe fn l_List_eraseReps___redArg(
    mut v_inst_6439_: *mut crate::leanh::LeanObject,
    mut v_as_6440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6441_ = crate::leanh::lean_alloc_closure(
        l_List_eraseDups___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6441_, 0, v_inst_6439_);
    v___x_6442_ = l_List_eraseRepsBy___redArg(v___f_6441_, v_as_6440_);
    return v___x_6442_;
}
pub unsafe fn l_List_eraseReps(
    mut v_00_u03b1_6443_: *mut crate::leanh::LeanObject,
    mut v_inst_6444_: *mut crate::leanh::LeanObject,
    mut v_as_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6446_ = l_List_eraseReps___redArg(v_inst_6444_, v_as_6445_);
    return v___x_6446_;
}
pub unsafe fn l_List_span_loop___redArg(
    mut v_p_6447_: *mut crate::leanh::LeanObject,
    mut v_a_6448_: *mut crate::leanh::LeanObject,
    mut v_a_6449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: u8 = 0;
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6465_: u8 = 0;
    let mut v_unused_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6448_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_6447_);
                    v___x_6450_ = l_List_reverse___redArg(v_a_6449_);
                    v___x_6451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6451_, 0, v___x_6450_);
                    crate::leanh::lean_ctor_set(v___x_6451_, 1, v_a_6448_);
                    return v___x_6451_;
                } else {
                    v_head_6452_ = crate::leanh::lean_ctor_get(v_a_6448_, 0);
                    v_tail_6453_ = crate::leanh::lean_ctor_get(v_a_6448_, 1);
                    crate::leanh::lean_inc_ref(v_p_6447_);
                    crate::leanh::lean_inc(v_head_6452_);
                    v___x_6454_ = crate::leanh::lean_apply_1(v_p_6447_, v_head_6452_);
                    v___x_6455_ = (crate::leanh::lean_unbox(v___x_6454_) as u8);
                    if v___x_6455_ == 0 {
                        crate::leanh::lean_dec_ref(v_p_6447_);
                        v___x_6456_ = l_List_reverse___redArg(v_a_6449_);
                        v___x_6457_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6457_, 0, v___x_6456_);
                        crate::leanh::lean_ctor_set(v___x_6457_, 1, v_a_6448_);
                        return v___x_6457_;
                    } else {
                        crate::leanh::lean_inc(v_tail_6453_);
                        crate::leanh::lean_inc(v_head_6452_);
                        v_isSharedCheck_6465_ = (!crate::leanh::lean_is_exclusive(v_a_6448_)) as u8;
                        if v_isSharedCheck_6465_ == 0 {
                            v_unused_6466_ = crate::leanh::lean_ctor_get(v_a_6448_, 1);
                            crate::leanh::lean_dec(v_unused_6466_);
                            v_unused_6467_ = crate::leanh::lean_ctor_get(v_a_6448_, 0);
                            crate::leanh::lean_dec(v_unused_6467_);
                            v___x_6459_ = v_a_6448_;
                            v_isShared_6460_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6448_);
                            v___x_6459_ = crate::leanh::lean_box(0);
                            v_isShared_6460_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6459_, 1, v_a_6449_);
                    v___x_6462_ = v___x_6459_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6464_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_head_6452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6464_, 1, v_a_6449_);
                    v___x_6462_ = v_reuseFailAlloc_6464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6448_ = v_tail_6453_;
                v_a_6449_ = v___x_6462_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_span_loop(
    mut v_00_u03b1_6468_: *mut crate::leanh::LeanObject,
    mut v_p_6469_: *mut crate::leanh::LeanObject,
    mut v_a_6470_: *mut crate::leanh::LeanObject,
    mut v_a_6471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6472_ = l_List_span_loop___redArg(v_p_6469_, v_a_6470_, v_a_6471_);
    return v___x_6472_;
}
pub unsafe fn l_List_span___redArg(
    mut v_p_6473_: *mut crate::leanh::LeanObject,
    mut v_as_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6475_ = crate::leanh::lean_box(0);
    v___x_6476_ = l_List_span_loop___redArg(v_p_6473_, v_as_6474_, v___x_6475_);
    return v___x_6476_;
}
pub unsafe fn l_List_span(
    mut v_00_u03b1_6477_: *mut crate::leanh::LeanObject,
    mut v_p_6478_: *mut crate::leanh::LeanObject,
    mut v_as_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = crate::leanh::lean_box(0);
    v___x_6481_ = l_List_span_loop___redArg(v_p_6478_, v_as_6479_, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn l_List_splitBy_loop___redArg(
    mut v_R_6482_: *mut crate::leanh::LeanObject,
    mut v_a_6483_: *mut crate::leanh::LeanObject,
    mut v_a_6484_: *mut crate::leanh::LeanObject,
    mut v_a_6485_: *mut crate::leanh::LeanObject,
    mut v_a_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6495_: u8 = 0;
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: u8 = 0;
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6483_) == 0 {
                    crate::leanh::lean_dec_ref(v_R_6482_);
                    v___x_6487_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6487_, 0, v_a_6484_);
                    crate::leanh::lean_ctor_set(v___x_6487_, 1, v_a_6485_);
                    v___x_6488_ = l_List_reverse___redArg(v___x_6487_);
                    v___x_6489_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6489_, 0, v___x_6488_);
                    crate::leanh::lean_ctor_set(v___x_6489_, 1, v_a_6486_);
                    v___x_6490_ = l_List_reverse___redArg(v___x_6489_);
                    return v___x_6490_;
                } else {
                    v_head_6491_ = crate::leanh::lean_ctor_get(v_a_6483_, 0);
                    v_tail_6492_ = crate::leanh::lean_ctor_get(v_a_6483_, 1);
                    v_isSharedCheck_6509_ = (!crate::leanh::lean_is_exclusive(v_a_6483_)) as u8;
                    if v_isSharedCheck_6509_ == 0 {
                        v___x_6494_ = v_a_6483_;
                        v_isShared_6495_ = v_isSharedCheck_6509_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6492_);
                        crate::leanh::lean_inc(v_head_6491_);
                        crate::leanh::lean_dec(v_a_6483_);
                        v___x_6494_ = crate::leanh::lean_box(0);
                        v_isShared_6495_ = v_isSharedCheck_6509_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_R_6482_);
                crate::leanh::lean_inc(v_head_6491_);
                crate::leanh::lean_inc(v_a_6484_);
                v___x_6496_ = crate::leanh::lean_apply_2(v_R_6482_, v_a_6484_, v_head_6491_);
                v___x_6497_ = (crate::leanh::lean_unbox(v___x_6496_) as u8);
                if v___x_6497_ == 0 {
                    v___x_6498_ = crate::leanh::lean_box(0);
                    if v_isShared_6495_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6494_, 1, v_a_6485_);
                        crate::leanh::lean_ctor_set(v___x_6494_, 0, v_a_6484_);
                        v___x_6500_ = v___x_6494_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6504_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6484_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 1, v_a_6485_);
                        v___x_6500_ = v_reuseFailAlloc_6504_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_6495_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6494_, 1, v_a_6485_);
                        crate::leanh::lean_ctor_set(v___x_6494_, 0, v_a_6484_);
                        v___x_6506_ = v___x_6494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6508_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_a_6484_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 1, v_a_6485_);
                        v___x_6506_ = v_reuseFailAlloc_6508_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6501_ = l_List_reverse___redArg(v___x_6500_);
                v___x_6502_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6502_, 0, v___x_6501_);
                crate::leanh::lean_ctor_set(v___x_6502_, 1, v_a_6486_);
                v_a_6483_ = v_tail_6492_;
                v_a_6484_ = v_head_6491_;
                v_a_6485_ = v___x_6498_;
                v_a_6486_ = v___x_6502_;
                state = 0;
                continue;
            }
            3 => {
                v_a_6483_ = v_tail_6492_;
                v_a_6484_ = v_head_6491_;
                v_a_6485_ = v___x_6506_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_splitBy_loop(
    mut v_00_u03b1_6510_: *mut crate::leanh::LeanObject,
    mut v_R_6511_: *mut crate::leanh::LeanObject,
    mut v_a_6512_: *mut crate::leanh::LeanObject,
    mut v_a_6513_: *mut crate::leanh::LeanObject,
    mut v_a_6514_: *mut crate::leanh::LeanObject,
    mut v_a_6515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6516_ =
        l_List_splitBy_loop___redArg(v_R_6511_, v_a_6512_, v_a_6513_, v_a_6514_, v_a_6515_);
    return v___x_6516_;
}
pub unsafe fn l_List_splitBy___redArg(
    mut v_R_6517_: *mut crate::leanh::LeanObject,
    mut v_x_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6518_) == 0 {
        let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_R_6517_);
        v___x_6519_ = crate::leanh::lean_box(0);
        return v___x_6519_;
    } else {
        let mut v_head_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_6520_ = crate::leanh::lean_ctor_get(v_x_6518_, 0);
        crate::leanh::lean_inc(v_head_6520_);
        v_tail_6521_ = crate::leanh::lean_ctor_get(v_x_6518_, 1);
        crate::leanh::lean_inc(v_tail_6521_);
        crate::leanh::lean_dec_ref_known(v_x_6518_, 2);
        v___x_6522_ = crate::leanh::lean_box(0);
        v___x_6523_ = l_List_splitBy_loop___redArg(
            v_R_6517_,
            v_tail_6521_,
            v_head_6520_,
            v___x_6522_,
            v___x_6522_,
        );
        return v___x_6523_;
    }
}
pub unsafe fn l_List_splitBy(
    mut v_00_u03b1_6524_: *mut crate::leanh::LeanObject,
    mut v_R_6525_: *mut crate::leanh::LeanObject,
    mut v_x_6526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6527_ = l_List_splitBy___redArg(v_R_6525_, v_x_6526_);
    return v___x_6527_;
}
pub unsafe fn l_List_removeAll___redArg___lam__0(
    mut v_inst_6528_: *mut crate::leanh::LeanObject,
    mut v_ys_6529_: *mut crate::leanh::LeanObject,
    mut v_x_6530_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6531_: u8 = 0;
    v___x_6531_ = l_List_elem___redArg(v_inst_6528_, v_x_6530_, v_ys_6529_);
    if v___x_6531_ == 0 {
        let mut v___x_6532_: u8 = 0;
        v___x_6532_ = 1;
        return v___x_6532_;
    } else {
        let mut v___x_6533_: u8 = 0;
        v___x_6533_ = 0;
        return v___x_6533_;
    }
}
pub unsafe fn l_List_removeAll___redArg___lam__0___boxed(
    mut v_inst_6534_: *mut crate::leanh::LeanObject,
    mut v_ys_6535_: *mut crate::leanh::LeanObject,
    mut v_x_6536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6537_: u8 = 0;
    let mut v_r_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6537_ = l_List_removeAll___redArg___lam__0(v_inst_6534_, v_ys_6535_, v_x_6536_);
    v_r_6538_ = crate::leanh::lean_box((v_res_6537_) as usize);
    return v_r_6538_;
}
pub unsafe fn l_List_removeAll___redArg(
    mut v_inst_6539_: *mut crate::leanh::LeanObject,
    mut v_xs_6540_: *mut crate::leanh::LeanObject,
    mut v_ys_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6542_ = crate::leanh::lean_alloc_closure(
        l_List_removeAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6542_, 0, v_inst_6539_);
    crate::leanh::lean_closure_set(v___f_6542_, 1, v_ys_6541_);
    v___x_6543_ = l_List_filter___redArg(v___f_6542_, v_xs_6540_);
    return v___x_6543_;
}
pub unsafe fn l_List_removeAll(
    mut v_00_u03b1_6544_: *mut crate::leanh::LeanObject,
    mut v_inst_6545_: *mut crate::leanh::LeanObject,
    mut v_xs_6546_: *mut crate::leanh::LeanObject,
    mut v_ys_6547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6548_ = l_List_removeAll___redArg(v_inst_6545_, v_xs_6546_, v_ys_6547_);
    return v___x_6548_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(
    mut v_ys_6549_: *mut crate::leanh::LeanObject,
    mut v_h__1_6550_: *mut crate::leanh::LeanObject,
    mut v_h__2_6551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_ys_6549_) == 0 {
        let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6551_);
        v___x_6552_ = crate::leanh::lean_box(0);
        v___x_6553_ = crate::leanh::lean_apply_1(v_h__1_6550_, v___x_6552_);
        return v___x_6553_;
    } else {
        let mut v_head_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6550_);
        v_head_6554_ = crate::leanh::lean_ctor_get(v_ys_6549_, 0);
        crate::leanh::lean_inc(v_head_6554_);
        v_tail_6555_ = crate::leanh::lean_ctor_get(v_ys_6549_, 1);
        crate::leanh::lean_inc(v_tail_6555_);
        crate::leanh::lean_dec_ref_known(v_ys_6549_, 2);
        v___x_6556_ = crate::leanh::lean_apply_2(v_h__2_6551_, v_head_6554_, v_tail_6555_);
        return v___x_6556_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(
    mut v_00_u03b1_6557_: *mut crate::leanh::LeanObject,
    mut v_motive_6558_: *mut crate::leanh::LeanObject,
    mut v_ys_6559_: *mut crate::leanh::LeanObject,
    mut v_h__1_6560_: *mut crate::leanh::LeanObject,
    mut v_h__2_6561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_ys_6559_) == 0 {
        let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6561_);
        v___x_6562_ = crate::leanh::lean_box(0);
        v___x_6563_ = crate::leanh::lean_apply_1(v_h__1_6560_, v___x_6562_);
        return v___x_6563_;
    } else {
        let mut v_head_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6560_);
        v_head_6564_ = crate::leanh::lean_ctor_get(v_ys_6559_, 0);
        crate::leanh::lean_inc(v_head_6564_);
        v_tail_6565_ = crate::leanh::lean_ctor_get(v_ys_6559_, 1);
        crate::leanh::lean_inc(v_tail_6565_);
        crate::leanh::lean_dec_ref_known(v_ys_6559_, 2);
        v___x_6566_ = crate::leanh::lean_apply_2(v_h__2_6561_, v_head_6564_, v_tail_6565_);
        return v___x_6566_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(
    mut v_x_6567_: *mut crate::leanh::LeanObject,
    mut v_x_6568_: *mut crate::leanh::LeanObject,
    mut v_h__1_6569_: *mut crate::leanh::LeanObject,
    mut v_h__2_6570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6567_) == 0 {
        let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6570_);
        v___x_6571_ = crate::leanh::lean_apply_1(v_h__1_6569_, v_x_6568_);
        return v___x_6571_;
    } else {
        let mut v_head_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6569_);
        v_head_6572_ = crate::leanh::lean_ctor_get(v_x_6567_, 0);
        crate::leanh::lean_inc(v_head_6572_);
        v_tail_6573_ = crate::leanh::lean_ctor_get(v_x_6567_, 1);
        crate::leanh::lean_inc(v_tail_6573_);
        crate::leanh::lean_dec_ref_known(v_x_6567_, 2);
        v___x_6574_ =
            crate::leanh::lean_apply_3(v_h__2_6570_, v_head_6572_, v_tail_6573_, v_x_6568_);
        return v___x_6574_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(
    mut v_00_u03b1_6575_: *mut crate::leanh::LeanObject,
    mut v_motive_6576_: *mut crate::leanh::LeanObject,
    mut v_x_6577_: *mut crate::leanh::LeanObject,
    mut v_x_6578_: *mut crate::leanh::LeanObject,
    mut v_h__1_6579_: *mut crate::leanh::LeanObject,
    mut v_h__2_6580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6577_) == 0 {
        let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6580_);
        v___x_6581_ = crate::leanh::lean_apply_1(v_h__1_6579_, v_x_6578_);
        return v___x_6581_;
    } else {
        let mut v_head_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6579_);
        v_head_6582_ = crate::leanh::lean_ctor_get(v_x_6577_, 0);
        crate::leanh::lean_inc(v_head_6582_);
        v_tail_6583_ = crate::leanh::lean_ctor_get(v_x_6577_, 1);
        crate::leanh::lean_inc(v_tail_6583_);
        crate::leanh::lean_dec_ref_known(v_x_6577_, 2);
        v___x_6584_ =
            crate::leanh::lean_apply_3(v_h__2_6580_, v_head_6582_, v_tail_6583_, v_x_6578_);
        return v___x_6584_;
    }
}
pub unsafe fn l_List_mapTR_loop___redArg(
    mut v_f_6585_: *mut crate::leanh::LeanObject,
    mut v_a_6586_: *mut crate::leanh::LeanObject,
    mut v_a_6587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6593_: u8 = 0;
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6586_) == 0 {
                    crate::leanh::lean_dec(v_f_6585_);
                    v___x_6588_ = l_List_reverse___redArg(v_a_6587_);
                    return v___x_6588_;
                } else {
                    v_head_6589_ = crate::leanh::lean_ctor_get(v_a_6586_, 0);
                    v_tail_6590_ = crate::leanh::lean_ctor_get(v_a_6586_, 1);
                    v_isSharedCheck_6599_ = (!crate::leanh::lean_is_exclusive(v_a_6586_)) as u8;
                    if v_isSharedCheck_6599_ == 0 {
                        v___x_6592_ = v_a_6586_;
                        v_isShared_6593_ = v_isSharedCheck_6599_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6590_);
                        crate::leanh::lean_inc(v_head_6589_);
                        crate::leanh::lean_dec(v_a_6586_);
                        v___x_6592_ = crate::leanh::lean_box(0);
                        v_isShared_6593_ = v_isSharedCheck_6599_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_6585_);
                v___x_6594_ = crate::leanh::lean_apply_1(v_f_6585_, v_head_6589_);
                if v_isShared_6593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6592_, 1, v_a_6587_);
                    crate::leanh::lean_ctor_set(v___x_6592_, 0, v___x_6594_);
                    v___x_6596_ = v___x_6592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 1, v_a_6587_);
                    v___x_6596_ = v_reuseFailAlloc_6598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6586_ = v_tail_6590_;
                v_a_6587_ = v___x_6596_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop(
    mut v_00_u03b1_6600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6601_: *mut crate::leanh::LeanObject,
    mut v_f_6602_: *mut crate::leanh::LeanObject,
    mut v_a_6603_: *mut crate::leanh::LeanObject,
    mut v_a_6604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = l_List_mapTR_loop___redArg(v_f_6602_, v_a_6603_, v_a_6604_);
    return v___x_6605_;
}
pub unsafe fn l_List_mapTR___redArg(
    mut v_f_6606_: *mut crate::leanh::LeanObject,
    mut v_as_6607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6608_ = crate::leanh::lean_box(0);
    v___x_6609_ = l_List_mapTR_loop___redArg(v_f_6606_, v_as_6607_, v___x_6608_);
    return v___x_6609_;
}
pub unsafe fn l_List_mapTR(
    mut v_00_u03b1_6610_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6611_: *mut crate::leanh::LeanObject,
    mut v_f_6612_: *mut crate::leanh::LeanObject,
    mut v_as_6613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6614_ = crate::leanh::lean_box(0);
    v___x_6615_ = l_List_mapTR_loop___redArg(v_f_6612_, v_as_6613_, v___x_6614_);
    return v___x_6615_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(
    mut v_x_6616_: *mut crate::leanh::LeanObject,
    mut v_x_6617_: *mut crate::leanh::LeanObject,
    mut v_h__1_6618_: *mut crate::leanh::LeanObject,
    mut v_h__2_6619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6616_) == 0 {
        let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6619_);
        v___x_6620_ = crate::leanh::lean_apply_1(v_h__1_6618_, v_x_6617_);
        return v___x_6620_;
    } else {
        let mut v_head_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6618_);
        v_head_6621_ = crate::leanh::lean_ctor_get(v_x_6616_, 0);
        crate::leanh::lean_inc(v_head_6621_);
        v_tail_6622_ = crate::leanh::lean_ctor_get(v_x_6616_, 1);
        crate::leanh::lean_inc(v_tail_6622_);
        crate::leanh::lean_dec_ref_known(v_x_6616_, 2);
        v___x_6623_ =
            crate::leanh::lean_apply_3(v_h__2_6619_, v_head_6621_, v_tail_6622_, v_x_6617_);
        return v___x_6623_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(
    mut v_00_u03b1_6624_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6625_: *mut crate::leanh::LeanObject,
    mut v_motive_6626_: *mut crate::leanh::LeanObject,
    mut v_x_6627_: *mut crate::leanh::LeanObject,
    mut v_x_6628_: *mut crate::leanh::LeanObject,
    mut v_h__1_6629_: *mut crate::leanh::LeanObject,
    mut v_h__2_6630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6627_) == 0 {
        let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6630_);
        v___x_6631_ = crate::leanh::lean_apply_1(v_h__1_6629_, v_x_6628_);
        return v___x_6631_;
    } else {
        let mut v_head_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6629_);
        v_head_6632_ = crate::leanh::lean_ctor_get(v_x_6627_, 0);
        crate::leanh::lean_inc(v_head_6632_);
        v_tail_6633_ = crate::leanh::lean_ctor_get(v_x_6627_, 1);
        crate::leanh::lean_inc(v_tail_6633_);
        crate::leanh::lean_dec_ref_known(v_x_6627_, 2);
        v___x_6634_ =
            crate::leanh::lean_apply_3(v_h__2_6630_, v_head_6632_, v_tail_6633_, v_x_6628_);
        return v___x_6634_;
    }
}
pub unsafe fn l_List_filterTR_loop___redArg(
    mut v_p_6635_: *mut crate::leanh::LeanObject,
    mut v_a_6636_: *mut crate::leanh::LeanObject,
    mut v_a_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6643_: u8 = 0;
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: u8 = 0;
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6636_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_6635_);
                    v___x_6638_ = l_List_reverse___redArg(v_a_6637_);
                    return v___x_6638_;
                } else {
                    v_head_6639_ = crate::leanh::lean_ctor_get(v_a_6636_, 0);
                    v_tail_6640_ = crate::leanh::lean_ctor_get(v_a_6636_, 1);
                    v_isSharedCheck_6651_ = (!crate::leanh::lean_is_exclusive(v_a_6636_)) as u8;
                    if v_isSharedCheck_6651_ == 0 {
                        v___x_6642_ = v_a_6636_;
                        v_isShared_6643_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6640_);
                        crate::leanh::lean_inc(v_head_6639_);
                        crate::leanh::lean_dec(v_a_6636_);
                        v___x_6642_ = crate::leanh::lean_box(0);
                        v_isShared_6643_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_p_6635_);
                crate::leanh::lean_inc(v_head_6639_);
                v___x_6644_ = crate::leanh::lean_apply_1(v_p_6635_, v_head_6639_);
                v___x_6645_ = (crate::leanh::lean_unbox(v___x_6644_) as u8);
                if v___x_6645_ == 0 {
                    crate::leanh::lean_del_object(v___x_6642_);
                    crate::leanh::lean_dec(v_head_6639_);
                    v_a_6636_ = v_tail_6640_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_6643_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6642_, 1, v_a_6637_);
                        v___x_6648_ = v___x_6642_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6650_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6650_, 0, v_head_6639_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6650_, 1, v_a_6637_);
                        v___x_6648_ = v_reuseFailAlloc_6650_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6636_ = v_tail_6640_;
                v_a_6637_ = v___x_6648_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop(
    mut v_00_u03b1_6652_: *mut crate::leanh::LeanObject,
    mut v_p_6653_: *mut crate::leanh::LeanObject,
    mut v_a_6654_: *mut crate::leanh::LeanObject,
    mut v_a_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6656_ = l_List_filterTR_loop___redArg(v_p_6653_, v_a_6654_, v_a_6655_);
    return v___x_6656_;
}
pub unsafe fn l_List_filterTR___redArg(
    mut v_p_6657_: *mut crate::leanh::LeanObject,
    mut v_as_6658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6659_ = crate::leanh::lean_box(0);
    v___x_6660_ = l_List_filterTR_loop___redArg(v_p_6657_, v_as_6658_, v___x_6659_);
    return v___x_6660_;
}
pub unsafe fn l_List_filterTR(
    mut v_00_u03b1_6661_: *mut crate::leanh::LeanObject,
    mut v_p_6662_: *mut crate::leanh::LeanObject,
    mut v_as_6663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6664_ = crate::leanh::lean_box(0);
    v___x_6665_ = l_List_filterTR_loop___redArg(v_p_6662_, v_as_6663_, v___x_6664_);
    return v___x_6665_;
}
pub unsafe fn l_List_replicateTR_loop___redArg(
    mut v_a_6666_: *mut crate::leanh::LeanObject,
    mut v_a_6667_: *mut crate::leanh::LeanObject,
    mut v_a_6668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6670_: u8 = 0;
    let mut v_one_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6669_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_6670_ = lean_nat_dec_eq(v_a_6667_, v_zero_6669_);
                if v_isZero_6670_ == 1 {
                    crate::leanh::lean_dec(v_a_6667_);
                    crate::leanh::lean_dec(v_a_6666_);
                    return v_a_6668_;
                } else {
                    v_one_6671_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_6672_ = lean_nat_sub(v_a_6667_, v_one_6671_);
                    crate::leanh::lean_dec(v_a_6667_);
                    crate::leanh::lean_inc(v_a_6666_);
                    v___x_6673_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6673_, 0, v_a_6666_);
                    crate::leanh::lean_ctor_set(v___x_6673_, 1, v_a_6668_);
                    v_a_6667_ = v_n_6672_;
                    v_a_6668_ = v___x_6673_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_replicateTR_loop(
    mut v_00_u03b1_6675_: *mut crate::leanh::LeanObject,
    mut v_a_6676_: *mut crate::leanh::LeanObject,
    mut v_a_6677_: *mut crate::leanh::LeanObject,
    mut v_a_6678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6679_ = l_List_replicateTR_loop___redArg(v_a_6676_, v_a_6677_, v_a_6678_);
    return v___x_6679_;
}
pub unsafe fn l_List_replicateTR___redArg(
    mut v_n_6680_: *mut crate::leanh::LeanObject,
    mut v_a_6681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6682_ = crate::leanh::lean_box(0);
    v___x_6683_ = l_List_replicateTR_loop___redArg(v_a_6681_, v_n_6680_, v___x_6682_);
    return v___x_6683_;
}
pub unsafe fn l_List_replicateTR(
    mut v_00_u03b1_6684_: *mut crate::leanh::LeanObject,
    mut v_n_6685_: *mut crate::leanh::LeanObject,
    mut v_a_6686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6687_ = l_List_replicateTR___redArg(v_n_6685_, v_a_6686_);
    return v___x_6687_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(
    mut v_x_6688_: *mut crate::leanh::LeanObject,
    mut v_x_6689_: *mut crate::leanh::LeanObject,
    mut v_h__1_6690_: *mut crate::leanh::LeanObject,
    mut v_h__2_6691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6693_: u8 = 0;
    v_zero_6692_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6693_ = lean_nat_dec_eq(v_x_6688_, v_zero_6692_);
    if v_isZero_6693_ == 1 {
        let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6691_);
        v___x_6694_ = crate::leanh::lean_apply_1(v_h__1_6690_, v_x_6689_);
        return v___x_6694_;
    } else {
        let mut v_one_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6690_);
        v_one_6695_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6696_ = lean_nat_sub(v_x_6688_, v_one_6695_);
        v___x_6697_ = crate::leanh::lean_apply_2(v_h__2_6691_, v_n_6696_, v_x_6689_);
        return v___x_6697_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_6698_: *mut crate::leanh::LeanObject,
    mut v_x_6699_: *mut crate::leanh::LeanObject,
    mut v_h__1_6700_: *mut crate::leanh::LeanObject,
    mut v_h__2_6701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6702_ =
        l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(
            v_x_6698_,
            v_x_6699_,
            v_h__1_6700_,
            v_h__2_6701_,
        );
    crate::leanh::lean_dec(v_x_6698_);
    return v_res_6702_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(
    mut v_00_u03b1_6703_: *mut crate::leanh::LeanObject,
    mut v_motive_6704_: *mut crate::leanh::LeanObject,
    mut v_x_6705_: *mut crate::leanh::LeanObject,
    mut v_x_6706_: *mut crate::leanh::LeanObject,
    mut v_h__1_6707_: *mut crate::leanh::LeanObject,
    mut v_h__2_6708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6710_: u8 = 0;
    v_zero_6709_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6710_ = lean_nat_dec_eq(v_x_6705_, v_zero_6709_);
    if v_isZero_6710_ == 1 {
        let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6708_);
        v___x_6711_ = crate::leanh::lean_apply_1(v_h__1_6707_, v_x_6706_);
        return v___x_6711_;
    } else {
        let mut v_one_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6707_);
        v_one_6712_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6713_ = lean_nat_sub(v_x_6705_, v_one_6712_);
        v___x_6714_ = crate::leanh::lean_apply_2(v_h__2_6708_, v_n_6713_, v_x_6706_);
        return v___x_6714_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(
    mut v_00_u03b1_6715_: *mut crate::leanh::LeanObject,
    mut v_motive_6716_: *mut crate::leanh::LeanObject,
    mut v_x_6717_: *mut crate::leanh::LeanObject,
    mut v_x_6718_: *mut crate::leanh::LeanObject,
    mut v_h__1_6719_: *mut crate::leanh::LeanObject,
    mut v_h__2_6720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6721_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(
        v_00_u03b1_6715_,
        v_motive_6716_,
        v_x_6717_,
        v_x_6718_,
        v_h__1_6719_,
        v_h__2_6720_,
    );
    crate::leanh::lean_dec(v_x_6717_);
    return v_res_6721_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(
    mut v_x_6722_: *mut crate::leanh::LeanObject,
    mut v_x_6723_: *mut crate::leanh::LeanObject,
    mut v_h__1_6724_: *mut crate::leanh::LeanObject,
    mut v_h__2_6725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6727_: u8 = 0;
    v_zero_6726_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6727_ = lean_nat_dec_eq(v_x_6722_, v_zero_6726_);
    if v_isZero_6727_ == 1 {
        let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6725_);
        v___x_6728_ = crate::leanh::lean_apply_1(v_h__1_6724_, v_x_6723_);
        return v___x_6728_;
    } else {
        let mut v_one_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6724_);
        v_one_6729_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6730_ = lean_nat_sub(v_x_6722_, v_one_6729_);
        v___x_6731_ = crate::leanh::lean_apply_2(v_h__2_6725_, v_n_6730_, v_x_6723_);
        return v___x_6731_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(
    mut v_x_6732_: *mut crate::leanh::LeanObject,
    mut v_x_6733_: *mut crate::leanh::LeanObject,
    mut v_h__1_6734_: *mut crate::leanh::LeanObject,
    mut v_h__2_6735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6736_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(
        v_x_6732_,
        v_x_6733_,
        v_h__1_6734_,
        v_h__2_6735_,
    );
    crate::leanh::lean_dec(v_x_6732_);
    return v_res_6736_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(
    mut v_00_u03b1_6737_: *mut crate::leanh::LeanObject,
    mut v_motive_6738_: *mut crate::leanh::LeanObject,
    mut v_x_6739_: *mut crate::leanh::LeanObject,
    mut v_x_6740_: *mut crate::leanh::LeanObject,
    mut v_h__1_6741_: *mut crate::leanh::LeanObject,
    mut v_h__2_6742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6744_: u8 = 0;
    v_zero_6743_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6744_ = lean_nat_dec_eq(v_x_6739_, v_zero_6743_);
    if v_isZero_6744_ == 1 {
        let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6742_);
        v___x_6745_ = crate::leanh::lean_apply_1(v_h__1_6741_, v_x_6740_);
        return v___x_6745_;
    } else {
        let mut v_one_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6741_);
        v_one_6746_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6747_ = lean_nat_sub(v_x_6739_, v_one_6746_);
        v___x_6748_ = crate::leanh::lean_apply_2(v_h__2_6742_, v_n_6747_, v_x_6740_);
        return v___x_6748_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(
    mut v_00_u03b1_6749_: *mut crate::leanh::LeanObject,
    mut v_motive_6750_: *mut crate::leanh::LeanObject,
    mut v_x_6751_: *mut crate::leanh::LeanObject,
    mut v_x_6752_: *mut crate::leanh::LeanObject,
    mut v_h__1_6753_: *mut crate::leanh::LeanObject,
    mut v_h__2_6754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6755_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(
        v_00_u03b1_6749_,
        v_motive_6750_,
        v_x_6751_,
        v_x_6752_,
        v_h__1_6753_,
        v_h__2_6754_,
    );
    crate::leanh::lean_dec(v_x_6751_);
    return v_res_6755_;
}
pub unsafe fn l_List_leftpadTR___redArg(
    mut v_n_6756_: *mut crate::leanh::LeanObject,
    mut v_a_6757_: *mut crate::leanh::LeanObject,
    mut v_l_6758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6759_ = l_List_lengthTR___redArg(v_l_6758_);
    v___x_6760_ = lean_nat_sub(v_n_6756_, v___x_6759_);
    crate::leanh::lean_dec(v___x_6759_);
    v___x_6761_ = l_List_replicateTR_loop___redArg(v_a_6757_, v___x_6760_, v_l_6758_);
    return v___x_6761_;
}
pub unsafe fn l_List_leftpadTR___redArg___boxed(
    mut v_n_6762_: *mut crate::leanh::LeanObject,
    mut v_a_6763_: *mut crate::leanh::LeanObject,
    mut v_l_6764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6765_ = l_List_leftpadTR___redArg(v_n_6762_, v_a_6763_, v_l_6764_);
    crate::leanh::lean_dec(v_n_6762_);
    return v_res_6765_;
}
pub unsafe fn l_List_leftpadTR(
    mut v_00_u03b1_6766_: *mut crate::leanh::LeanObject,
    mut v_n_6767_: *mut crate::leanh::LeanObject,
    mut v_a_6768_: *mut crate::leanh::LeanObject,
    mut v_l_6769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6770_ = l_List_lengthTR___redArg(v_l_6769_);
    v___x_6771_ = lean_nat_sub(v_n_6767_, v___x_6770_);
    crate::leanh::lean_dec(v___x_6770_);
    v___x_6772_ = l_List_replicateTR_loop___redArg(v_a_6768_, v___x_6771_, v_l_6769_);
    return v___x_6772_;
}
pub unsafe fn l_List_leftpadTR___boxed(
    mut v_00_u03b1_6773_: *mut crate::leanh::LeanObject,
    mut v_n_6774_: *mut crate::leanh::LeanObject,
    mut v_a_6775_: *mut crate::leanh::LeanObject,
    mut v_l_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6777_ = l_List_leftpadTR(v_00_u03b1_6773_, v_n_6774_, v_a_6775_, v_l_6776_);
    crate::leanh::lean_dec(v_n_6774_);
    return v_res_6777_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0___redArg(
    mut v_init_6778_: *mut crate::leanh::LeanObject,
    mut v_x_6779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v_fst_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6789_: u8 = 0;
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6795_: u8 = 0;
    let mut v___x_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6805_: u8 = 0;
    let mut v_isSharedCheck_6806_: u8 = 0;
    let mut v_isSharedCheck_6807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6779_) == 0 {
                    crate::leanh::lean_inc_ref(v_init_6778_);
                    return v_init_6778_;
                } else {
                    v_head_6780_ = crate::leanh::lean_ctor_get(v_x_6779_, 0);
                    v_tail_6781_ = crate::leanh::lean_ctor_get(v_x_6779_, 1);
                    v_isSharedCheck_6807_ = (!crate::leanh::lean_is_exclusive(v_x_6779_)) as u8;
                    if v_isSharedCheck_6807_ == 0 {
                        v___x_6783_ = v_x_6779_;
                        v_isShared_6784_ = v_isSharedCheck_6807_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6781_);
                        crate::leanh::lean_inc(v_head_6780_);
                        crate::leanh::lean_dec(v_x_6779_);
                        v___x_6783_ = crate::leanh::lean_box(0);
                        v_isShared_6784_ = v_isSharedCheck_6807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6785_ = crate::leanh::lean_ctor_get(v_head_6780_, 0);
                v_snd_6786_ = crate::leanh::lean_ctor_get(v_head_6780_, 1);
                v_isSharedCheck_6806_ = (!crate::leanh::lean_is_exclusive(v_head_6780_)) as u8;
                if v_isSharedCheck_6806_ == 0 {
                    v___x_6788_ = v_head_6780_;
                    v_isShared_6789_ = v_isSharedCheck_6806_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6786_);
                    crate::leanh::lean_inc(v_fst_6785_);
                    crate::leanh::lean_dec(v_head_6780_);
                    v___x_6788_ = crate::leanh::lean_box(0);
                    v_isShared_6789_ = v_isSharedCheck_6806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6790_ =
                    l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6778_, v_tail_6781_);
                v_fst_6791_ = crate::leanh::lean_ctor_get(v___x_6790_, 0);
                v_snd_6792_ = crate::leanh::lean_ctor_get(v___x_6790_, 1);
                v_isSharedCheck_6805_ = (!crate::leanh::lean_is_exclusive(v___x_6790_)) as u8;
                if v_isSharedCheck_6805_ == 0 {
                    v___x_6794_ = v___x_6790_;
                    v_isShared_6795_ = v_isSharedCheck_6805_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6792_);
                    crate::leanh::lean_inc(v_fst_6791_);
                    crate::leanh::lean_dec(v___x_6790_);
                    v___x_6794_ = crate::leanh::lean_box(0);
                    v_isShared_6795_ = v_isSharedCheck_6805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6784_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6783_, 1, v_fst_6791_);
                    crate::leanh::lean_ctor_set(v___x_6783_, 0, v_fst_6785_);
                    v___x_6797_ = v___x_6783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6804_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 0, v_fst_6785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 1, v_fst_6791_);
                    v___x_6797_ = v_reuseFailAlloc_6804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6789_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6788_, 1);
                    crate::leanh::lean_ctor_set(v___x_6788_, 1, v_snd_6792_);
                    crate::leanh::lean_ctor_set(v___x_6788_, 0, v_snd_6786_);
                    v___x_6799_ = v___x_6788_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6803_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_snd_6786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 1, v_snd_6792_);
                    v___x_6799_ = v_reuseFailAlloc_6803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6794_, 1, v___x_6799_);
                    crate::leanh::lean_ctor_set(v___x_6794_, 0, v___x_6797_);
                    v___x_6801_ = v___x_6794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 0, v___x_6797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 1, v___x_6799_);
                    v___x_6801_ = v_reuseFailAlloc_6802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0___redArg___boxed(
    mut v_init_6808_: *mut crate::leanh::LeanObject,
    mut v_x_6809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6810_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6808_, v_x_6809_);
    crate::leanh::lean_dec_ref(v_init_6808_);
    return v_res_6810_;
}
pub unsafe fn l_List_unzipTR___redArg(
    mut v_l_6811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6812_ = l_List_partition___redArg___closed__0;
    v___x_6813_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_6812_, v_l_6811_);
    return v___x_6813_;
}
pub unsafe fn l_List_unzipTR(
    mut v_00_u03b1_6814_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6815_: *mut crate::leanh::LeanObject,
    mut v_l_6816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6817_ = l_List_unzipTR___redArg(v_l_6816_);
    return v___x_6817_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0(
    mut v_00_u03b1_6818_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6819_: *mut crate::leanh::LeanObject,
    mut v_init_6820_: *mut crate::leanh::LeanObject,
    mut v_x_6821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6822_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6820_, v_x_6821_);
    return v___x_6822_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0___boxed(
    mut v_00_u03b1_6823_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6824_: *mut crate::leanh::LeanObject,
    mut v_init_6825_: *mut crate::leanh::LeanObject,
    mut v_x_6826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6827_ = l_List_foldr___at___00List_unzipTR_spec__0(
        v_00_u03b1_6823_,
        v_00_u03b2_6824_,
        v_init_6825_,
        v_x_6826_,
    );
    crate::leanh::lean_dec_ref(v_init_6825_);
    return v_res_6827_;
}
pub unsafe fn l_List_range_x27TR_go(
    mut v_step_6828_: *mut crate::leanh::LeanObject,
    mut v_a_6829_: *mut crate::leanh::LeanObject,
    mut v_a_6830_: *mut crate::leanh::LeanObject,
    mut v_a_6831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6833_: u8 = 0;
    let mut v_one_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6832_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_6833_ = lean_nat_dec_eq(v_a_6829_, v_zero_6832_);
                if v_isZero_6833_ == 1 {
                    crate::leanh::lean_dec(v_a_6830_);
                    crate::leanh::lean_dec(v_a_6829_);
                    return v_a_6831_;
                } else {
                    v_one_6834_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_6835_ = lean_nat_sub(v_a_6829_, v_one_6834_);
                    crate::leanh::lean_dec(v_a_6829_);
                    v___x_6836_ = lean_nat_sub(v_a_6830_, v_step_6828_);
                    crate::leanh::lean_dec(v_a_6830_);
                    crate::leanh::lean_inc(v___x_6836_);
                    v___x_6837_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6837_, 0, v___x_6836_);
                    crate::leanh::lean_ctor_set(v___x_6837_, 1, v_a_6831_);
                    v_a_6829_ = v_n_6835_;
                    v_a_6830_ = v___x_6836_;
                    v_a_6831_ = v___x_6837_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_range_x27TR_go___boxed(
    mut v_step_6839_: *mut crate::leanh::LeanObject,
    mut v_a_6840_: *mut crate::leanh::LeanObject,
    mut v_a_6841_: *mut crate::leanh::LeanObject,
    mut v_a_6842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6843_ = l_List_range_x27TR_go(v_step_6839_, v_a_6840_, v_a_6841_, v_a_6842_);
    crate::leanh::lean_dec(v_step_6839_);
    return v_res_6843_;
}
pub unsafe fn l_List_range_x27TR(
    mut v_s_6844_: *mut crate::leanh::LeanObject,
    mut v_n_6845_: *mut crate::leanh::LeanObject,
    mut v_step_6846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6847_ = lean_nat_mul(v_step_6846_, v_n_6845_);
    v___x_6848_ = lean_nat_add(v_s_6844_, v___x_6847_);
    crate::leanh::lean_dec(v___x_6847_);
    v___x_6849_ = crate::leanh::lean_box(0);
    v___x_6850_ = l_List_range_x27TR_go(v_step_6846_, v_n_6845_, v___x_6848_, v___x_6849_);
    return v___x_6850_;
}
pub unsafe fn l_List_range_x27TR___boxed(
    mut v_s_6851_: *mut crate::leanh::LeanObject,
    mut v_n_6852_: *mut crate::leanh::LeanObject,
    mut v_step_6853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6854_ = l_List_range_x27TR(v_s_6851_, v_n_6852_, v_step_6853_);
    crate::leanh::lean_dec(v_step_6853_);
    crate::leanh::lean_dec(v_s_6851_);
    return v_res_6854_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(
    mut v_x_6855_: *mut crate::leanh::LeanObject,
    mut v_x_6856_: *mut crate::leanh::LeanObject,
    mut v_x_6857_: *mut crate::leanh::LeanObject,
    mut v_h__1_6858_: *mut crate::leanh::LeanObject,
    mut v_h__2_6859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6861_: u8 = 0;
    v_zero_6860_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6861_ = lean_nat_dec_eq(v_x_6855_, v_zero_6860_);
    if v_isZero_6861_ == 1 {
        let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6859_);
        v___x_6862_ = crate::leanh::lean_apply_2(v_h__1_6858_, v_x_6856_, v_x_6857_);
        return v___x_6862_;
    } else {
        let mut v_one_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6858_);
        v_one_6863_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6864_ = lean_nat_sub(v_x_6855_, v_one_6863_);
        v___x_6865_ = crate::leanh::lean_apply_3(v_h__2_6859_, v_n_6864_, v_x_6856_, v_x_6857_);
        return v___x_6865_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(
    mut v_x_6866_: *mut crate::leanh::LeanObject,
    mut v_x_6867_: *mut crate::leanh::LeanObject,
    mut v_x_6868_: *mut crate::leanh::LeanObject,
    mut v_h__1_6869_: *mut crate::leanh::LeanObject,
    mut v_h__2_6870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6871_ =
        l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(
            v_x_6866_,
            v_x_6867_,
            v_x_6868_,
            v_h__1_6869_,
            v_h__2_6870_,
        );
    crate::leanh::lean_dec(v_x_6866_);
    return v_res_6871_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(
    mut v_motive_6872_: *mut crate::leanh::LeanObject,
    mut v_x_6873_: *mut crate::leanh::LeanObject,
    mut v_x_6874_: *mut crate::leanh::LeanObject,
    mut v_x_6875_: *mut crate::leanh::LeanObject,
    mut v_h__1_6876_: *mut crate::leanh::LeanObject,
    mut v_h__2_6877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6879_: u8 = 0;
    v_zero_6878_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_6879_ = lean_nat_dec_eq(v_x_6873_, v_zero_6878_);
    if v_isZero_6879_ == 1 {
        let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_6877_);
        v___x_6880_ = crate::leanh::lean_apply_2(v_h__1_6876_, v_x_6874_, v_x_6875_);
        return v___x_6880_;
    } else {
        let mut v_one_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6876_);
        v_one_6881_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_6882_ = lean_nat_sub(v_x_6873_, v_one_6881_);
        v___x_6883_ = crate::leanh::lean_apply_3(v_h__2_6877_, v_n_6882_, v_x_6874_, v_x_6875_);
        return v___x_6883_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(
    mut v_motive_6884_: *mut crate::leanh::LeanObject,
    mut v_x_6885_: *mut crate::leanh::LeanObject,
    mut v_x_6886_: *mut crate::leanh::LeanObject,
    mut v_x_6887_: *mut crate::leanh::LeanObject,
    mut v_h__1_6888_: *mut crate::leanh::LeanObject,
    mut v_h__2_6889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6890_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(
        v_motive_6884_,
        v_x_6885_,
        v_x_6886_,
        v_x_6887_,
        v_h__1_6888_,
        v_h__2_6889_,
    );
    crate::leanh::lean_dec(v_x_6885_);
    return v_res_6890_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
    mut v_sep_6891_: *mut crate::leanh::LeanObject,
    mut v_init_6892_: *mut crate::leanh::LeanObject,
    mut v_x_6893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6893_) == 0 {
                    crate::leanh::lean_dec(v_sep_6891_);
                    crate::leanh::lean_inc(v_init_6892_);
                    return v_init_6892_;
                } else {
                    v_head_6894_ = crate::leanh::lean_ctor_get(v_x_6893_, 0);
                    v_tail_6895_ = crate::leanh::lean_ctor_get(v_x_6893_, 1);
                    v_isSharedCheck_6904_ = (!crate::leanh::lean_is_exclusive(v_x_6893_)) as u8;
                    if v_isSharedCheck_6904_ == 0 {
                        v___x_6897_ = v_x_6893_;
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6895_);
                        crate::leanh::lean_inc(v_head_6894_);
                        crate::leanh::lean_dec(v_x_6893_);
                        v___x_6897_ = crate::leanh::lean_box(0);
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_sep_6891_);
                v___x_6899_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
                    v_sep_6891_,
                    v_init_6892_,
                    v_tail_6895_,
                );
                if v_isShared_6898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6897_, 1, v___x_6899_);
                    v___x_6901_ = v___x_6897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6903_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_head_6894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 1, v___x_6899_);
                    v___x_6901_ = v_reuseFailAlloc_6903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6902_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6902_, 0, v_sep_6891_);
                crate::leanh::lean_ctor_set(v___x_6902_, 1, v___x_6901_);
                return v___x_6902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(
    mut v_sep_6905_: *mut crate::leanh::LeanObject,
    mut v_init_6906_: *mut crate::leanh::LeanObject,
    mut v_x_6907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6908_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
        v_sep_6905_,
        v_init_6906_,
        v_x_6907_,
    );
    crate::leanh::lean_dec(v_init_6906_);
    return v_res_6908_;
}
pub unsafe fn l_List_intersperseTR___redArg(
    mut v_sep_6909_: *mut crate::leanh::LeanObject,
    mut v_x_6910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6915_: u8 = 0;
    let mut v_head_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6930_: u8 = 0;
    let mut v_isSharedCheck_6931_: u8 = 0;
    let mut v_unused_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6910_) == 0 {
                    crate::leanh::lean_dec(v_sep_6909_);
                    return v_x_6910_;
                } else {
                    v_tail_6911_ = crate::leanh::lean_ctor_get(v_x_6910_, 1);
                    crate::leanh::lean_inc(v_tail_6911_);
                    if crate::leanh::lean_obj_tag(v_tail_6911_) == 0 {
                        crate::leanh::lean_dec(v_sep_6909_);
                        return v_x_6910_;
                    } else {
                        v_head_6912_ = crate::leanh::lean_ctor_get(v_x_6910_, 0);
                        v_isSharedCheck_6931_ = (!crate::leanh::lean_is_exclusive(v_x_6910_)) as u8;
                        if v_isSharedCheck_6931_ == 0 {
                            v_unused_6932_ = crate::leanh::lean_ctor_get(v_x_6910_, 1);
                            crate::leanh::lean_dec(v_unused_6932_);
                            v___x_6914_ = v_x_6910_;
                            v_isShared_6915_ = v_isSharedCheck_6931_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_6912_);
                            crate::leanh::lean_dec(v_x_6910_);
                            v___x_6914_ = crate::leanh::lean_box(0);
                            v_isShared_6915_ = v_isSharedCheck_6931_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_head_6916_ = crate::leanh::lean_ctor_get(v_tail_6911_, 0);
                v_tail_6917_ = crate::leanh::lean_ctor_get(v_tail_6911_, 1);
                v_isSharedCheck_6930_ = (!crate::leanh::lean_is_exclusive(v_tail_6911_)) as u8;
                if v_isSharedCheck_6930_ == 0 {
                    v___x_6919_ = v_tail_6911_;
                    v_isShared_6920_ = v_isSharedCheck_6930_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_6917_);
                    crate::leanh::lean_inc(v_head_6916_);
                    crate::leanh::lean_dec(v_tail_6911_);
                    v___x_6919_ = crate::leanh::lean_box(0);
                    v_isShared_6920_ = v_isSharedCheck_6930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6921_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_sep_6909_);
                v___x_6922_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
                    v_sep_6909_,
                    v___x_6921_,
                    v_tail_6917_,
                );
                if v_isShared_6920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6919_, 1, v___x_6922_);
                    v___x_6924_ = v___x_6919_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6929_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_head_6916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 1, v___x_6922_);
                    v___x_6924_ = v_reuseFailAlloc_6929_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6914_, 1, v___x_6924_);
                    crate::leanh::lean_ctor_set(v___x_6914_, 0, v_sep_6909_);
                    v___x_6926_ = v___x_6914_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6928_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_sep_6909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 1, v___x_6924_);
                    v___x_6926_ = v_reuseFailAlloc_6928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6927_, 0, v_head_6912_);
                crate::leanh::lean_ctor_set(v___x_6927_, 1, v___x_6926_);
                return v___x_6927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_intersperseTR(
    mut v_00_u03b1_6933_: *mut crate::leanh::LeanObject,
    mut v_sep_6934_: *mut crate::leanh::LeanObject,
    mut v_x_6935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6936_ = l_List_intersperseTR___redArg(v_sep_6934_, v_x_6935_);
    return v___x_6936_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0(
    mut v_00_u03b1_6937_: *mut crate::leanh::LeanObject,
    mut v_sep_6938_: *mut crate::leanh::LeanObject,
    mut v_init_6939_: *mut crate::leanh::LeanObject,
    mut v_x_6940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6941_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
        v_sep_6938_,
        v_init_6939_,
        v_x_6940_,
    );
    return v___x_6941_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___boxed(
    mut v_00_u03b1_6942_: *mut crate::leanh::LeanObject,
    mut v_sep_6943_: *mut crate::leanh::LeanObject,
    mut v_init_6944_: *mut crate::leanh::LeanObject,
    mut v_x_6945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6946_ = l_List_foldr___at___00List_intersperseTR_spec__0(
        v_00_u03b1_6942_,
        v_sep_6943_,
        v_init_6944_,
        v_x_6945_,
    );
    crate::leanh::lean_dec(v_init_6944_);
    return v_res_6946_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(
    mut v_x_6947_: *mut crate::leanh::LeanObject,
    mut v_h__1_6948_: *mut crate::leanh::LeanObject,
    mut v_h__2_6949_: *mut crate::leanh::LeanObject,
    mut v_h__3_6950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6947_) == 0 {
        let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6950_);
        crate::leanh::lean_dec(v_h__2_6949_);
        v___x_6951_ = crate::leanh::lean_box(0);
        v___x_6952_ = crate::leanh::lean_apply_1(v_h__1_6948_, v___x_6951_);
        return v___x_6952_;
    } else {
        let mut v_tail_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6948_);
        v_tail_6953_ = crate::leanh::lean_ctor_get(v_x_6947_, 1);
        if crate::leanh::lean_obj_tag(v_tail_6953_) == 0 {
            let mut v_head_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6950_);
            v_head_6954_ = crate::leanh::lean_ctor_get(v_x_6947_, 0);
            crate::leanh::lean_inc(v_head_6954_);
            crate::leanh::lean_dec_ref_known(v_x_6947_, 2);
            v___x_6955_ = crate::leanh::lean_apply_1(v_h__2_6949_, v_head_6954_);
            return v___x_6955_;
        } else {
            let mut v_head_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_6953_);
            crate::leanh::lean_dec(v_h__2_6949_);
            v_head_6956_ = crate::leanh::lean_ctor_get(v_x_6947_, 0);
            crate::leanh::lean_inc(v_head_6956_);
            crate::leanh::lean_dec_ref_known(v_x_6947_, 2);
            v_head_6957_ = crate::leanh::lean_ctor_get(v_tail_6953_, 0);
            crate::leanh::lean_inc(v_head_6957_);
            v_tail_6958_ = crate::leanh::lean_ctor_get(v_tail_6953_, 1);
            crate::leanh::lean_inc(v_tail_6958_);
            crate::leanh::lean_dec_ref_known(v_tail_6953_, 2);
            v___x_6959_ =
                crate::leanh::lean_apply_3(v_h__3_6950_, v_head_6956_, v_head_6957_, v_tail_6958_);
            return v___x_6959_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(
    mut v_00_u03b1_6960_: *mut crate::leanh::LeanObject,
    mut v_motive_6961_: *mut crate::leanh::LeanObject,
    mut v_x_6962_: *mut crate::leanh::LeanObject,
    mut v_h__1_6963_: *mut crate::leanh::LeanObject,
    mut v_h__2_6964_: *mut crate::leanh::LeanObject,
    mut v_h__3_6965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6962_) == 0 {
        let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_6965_);
        crate::leanh::lean_dec(v_h__2_6964_);
        v___x_6966_ = crate::leanh::lean_box(0);
        v___x_6967_ = crate::leanh::lean_apply_1(v_h__1_6963_, v___x_6966_);
        return v___x_6967_;
    } else {
        let mut v_tail_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_6963_);
        v_tail_6968_ = crate::leanh::lean_ctor_get(v_x_6962_, 1);
        if crate::leanh::lean_obj_tag(v_tail_6968_) == 0 {
            let mut v_head_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_6965_);
            v_head_6969_ = crate::leanh::lean_ctor_get(v_x_6962_, 0);
            crate::leanh::lean_inc(v_head_6969_);
            crate::leanh::lean_dec_ref_known(v_x_6962_, 2);
            v___x_6970_ = crate::leanh::lean_apply_1(v_h__2_6964_, v_head_6969_);
            return v___x_6970_;
        } else {
            let mut v_head_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_6968_);
            crate::leanh::lean_dec(v_h__2_6964_);
            v_head_6971_ = crate::leanh::lean_ctor_get(v_x_6962_, 0);
            crate::leanh::lean_inc(v_head_6971_);
            crate::leanh::lean_dec_ref_known(v_x_6962_, 2);
            v_head_6972_ = crate::leanh::lean_ctor_get(v_tail_6968_, 0);
            crate::leanh::lean_inc(v_head_6972_);
            v_tail_6973_ = crate::leanh::lean_ctor_get(v_tail_6968_, 1);
            crate::leanh::lean_inc(v_tail_6973_);
            crate::leanh::lean_dec_ref_known(v_tail_6968_, 2);
            v___x_6974_ =
                crate::leanh::lean_apply_3(v_h__3_6965_, v_head_6971_, v_head_6972_, v_tail_6973_);
            return v___x_6974_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Zero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_lex___auto__1 = _init_l_List_lex___auto__1();
    crate::leanh::lean_mark_persistent(l_List_lex___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Zero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Basic(builtin);
}

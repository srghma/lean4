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
pub static l_List_lex___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_List_lex___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_List_lex___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_List_lex___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_List_lex___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__3_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_List_lex___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__6_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_List_lex___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__6_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_List_lex___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__10_value: leanh::LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_List_lex___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__10_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__14_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_List_lex___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__15_value: leanh::LeanStringObject<6> =
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
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_List_lex___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__15_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__15_value)
                as *mut leanh::LeanObject,
            7932075773091973500 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__17_value: leanh::LeanStringObject<15> =
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
            104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
        ],
    };
static mut l_List_lex___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__17_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__18_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__18_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__17_value)
                as *mut leanh::LeanObject,
            7306243862518720553 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__19_value: leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_List_lex___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__19_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__22_value: leanh::LeanStringObject<12> =
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
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_List_lex___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__23_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__22_value)
                as *mut leanh::LeanObject,
            9871775667037945883 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__24_value: leanh::LeanStringObject<12> =
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
        m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
    };
static mut l_List_lex___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__24_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__25: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__28: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__31_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__32: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__33_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 60, 95, 0],
    };
static mut l_List_lex___auto__1___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__33_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__34_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__33_value)
                as *mut leanh::LeanObject,
            6883052497475924672 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__35_value: leanh::LeanStringObject<5> =
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
        m_data: [99, 100, 111, 116, 0],
    };
static mut l_List_lex___auto__1___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__35_value) as *mut leanh::LeanObject;
static l_List_lex___auto__1___closed__36_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__36_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_List_lex___auto__1___closed__36_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_lex___auto__1___closed__36_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_lex___auto__1___closed__35_value)
                as *mut leanh::LeanObject,
            6167508377434939095 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_lex___auto__1___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__36_value) as *mut leanh::LeanObject;
pub static l_List_lex___auto__1___closed__37_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_List_lex___auto__1___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__37_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__38: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__39: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__40: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__41: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__42: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__43_value: leanh::LeanStringObject<2> =
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
        m_data: [60, 0],
    };
static mut l_List_lex___auto__1___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__43_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__44: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__46_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__46: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__47: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__48_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__48: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_lex___auto__1___closed__49_value: leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_List_lex___auto__1___closed__49: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_lex___auto__1___closed__49_value) as *mut leanh::LeanObject;
static mut l_List_lex___auto__1___closed__50_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__50: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__51_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__51: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__52_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__52: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__53_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__53: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__54_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__54: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__55_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__55: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__56_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__56: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__57_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__57: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__58_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__58: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__59_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__59: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_lex___auto__1___closed__60_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_lex___auto__1___closed__60: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_List_lex___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_instAppend___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_appendTR as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_List_instAppend___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instAppend___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_partition___redArg___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_List_partition___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_partition___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_List_term___x3c_x2b___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_List_term___x3c_x2b___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__1_value)
        as *mut leanh::LeanObject;
static l_List_term___x3c_x2b___00__closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            9582258842178272501 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x2b___00__closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__1_value)
                as *mut leanh::LeanObject,
            5032644207915418729 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__3_value: leanh::LeanStringObject<8> =
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
static mut l_List_term___x3c_x2b___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__5_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 60, 43, 32, 0],
    };
static mut l_List_term___x3c_x2b___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__7_value: leanh::LeanStringObject<5> =
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
static mut l_List_term___x3c_x2b___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__7_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__8_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b___00__closed__11_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__2_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static mut l_List_term___x3c_x2b__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_lex___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__0_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 117, 98, 108, 105, 115, 116, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut leanh::LeanObject,3971429882733148553 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2_value) as *mut leanh::LeanObject,13118543908479833671 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__5_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__9_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 43, 58, 95, 0],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            9582258842178272501 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x2b_x3a___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__0_value)
                as *mut leanh::LeanObject,
            11338394075872571116 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 43, 58, 32, 0],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x2b_x3a___00__closed__5_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x2b_x3a___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_List_term___x3c_x2b_x3a__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x2b_x3a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 115, 80, 114, 101, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject,4340084101528514341 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject,11033310021417905675 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 60, 58, 43, 95, 0],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            9582258842178272501 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x3a_x2b___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            3367210673871417624 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [32, 60, 58, 43, 32, 0],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b___00__closed__5_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_List_term___x3c_x3a_x2b__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 115, 83, 117, 102, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut leanh::LeanObject,2296567635584722319 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0_value) as *mut leanh::LeanObject,12518011436897045665 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 58, 43, 58, 95, 0],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            9582258842178272501 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__0_value)
                as *mut leanh::LeanObject,
            5638408978683487334 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 60, 58, 43, 58, 32, 0],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x3c_x3a_x2b_x3a___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_List_term___x3c_x3a_x2b_x3a__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x3c_x3a_x2b_x3a___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 115, 73, 110, 102, 105, 120, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject,10897887609920352419 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0_value) as *mut leanh::LeanObject,9055159914511838349 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_term___x7e___00__closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 126, 95, 0],
    };
static mut l_List_term___x7e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__0_value) as *mut leanh::LeanObject;
static l_List_term___x7e___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value)
                as *mut leanh::LeanObject,
            9582258842178272501 as *mut leanh::LeanObject,
        ],
    };
pub static l_List_term___x7e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__0_value)
                as *mut leanh::LeanObject,
            17617384562182800008 as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_List_term___x7e___00__closed__2_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 126, 32, 0],
    };
static mut l_List_term___x7e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_List_term___x7e___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_List_term___x7e___00__closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_List_term___x7e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_List_term___x7e___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__4_value) as *mut leanh::LeanObject;
pub static l_List_term___x7e___00__closed__5_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_List_term___x7e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_term___x7e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_term___x7e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__5_value) as *mut leanh::LeanObject;
pub static mut l_List_term___x7e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_term___x7e___00__closed__5_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 101, 114, 109, 0]};
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut leanh::LeanObject,6725144291058853725 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2_value) as *mut leanh::LeanObject;
static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_term___x3c_x2b___00__closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0_value) as *mut leanh::LeanObject,6626821958560496499 as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__3_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__6_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_List_Basic_0__List_set_match__1_splitter___redArg(
    mut v_x_3488_: *mut leanh::LeanObject,
    mut v_x_3489_: *mut leanh::LeanObject,
    mut v_x_3490_: *mut leanh::LeanObject,
    mut v_h__1_3491_: *mut leanh::LeanObject,
    mut v_h__2_3492_: *mut leanh::LeanObject,
    mut v_h__3_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3488_) == 0 {
        let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3492_);
        leanh::lean_dec(v_h__1_3491_);
        v___x_3494_ = leanh::lean_apply_2(v_h__3_3493_, v_x_3489_, v_x_3490_);
        return v___x_3494_;
    } else {
        let mut v_head_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_3498_: u8 = 0;
        leanh::lean_dec(v_h__3_3493_);
        v_head_3495_ = leanh::lean_ctor_get(v_x_3488_, 0);
        leanh::lean_inc(v_head_3495_);
        v_tail_3496_ = leanh::lean_ctor_get(v_x_3488_, 1);
        leanh::lean_inc(v_tail_3496_);
        leanh::lean_dec_ref_known(v_x_3488_, 2);
        v_zero_3497_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_3498_ = lean_nat_dec_eq(v_x_3489_, v_zero_3497_);
        if v_isZero_3498_ == 1 {
            let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3492_);
            leanh::lean_dec(v_x_3489_);
            v___x_3499_ =
                leanh::lean_apply_3(v_h__1_3491_, v_head_3495_, v_tail_3496_, v_x_3490_);
            return v___x_3499_;
        } else {
            let mut v_one_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_3491_);
            v_one_3500_ = leanh::lean_unsigned_to_nat(1);
            v_n_3501_ = lean_nat_sub(v_x_3489_, v_one_3500_);
            leanh::lean_dec(v_x_3489_);
            v___x_3502_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_3503_: *mut leanh::LeanObject,
    mut v_motive_3504_: *mut leanh::LeanObject,
    mut v_x_3505_: *mut leanh::LeanObject,
    mut v_x_3506_: *mut leanh::LeanObject,
    mut v_x_3507_: *mut leanh::LeanObject,
    mut v_h__1_3508_: *mut leanh::LeanObject,
    mut v_h__2_3509_: *mut leanh::LeanObject,
    mut v_h__3_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3505_) == 0 {
        let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3509_);
        leanh::lean_dec(v_h__1_3508_);
        v___x_3511_ = leanh::lean_apply_2(v_h__3_3510_, v_x_3506_, v_x_3507_);
        return v___x_3511_;
    } else {
        let mut v_head_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zero_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_3515_: u8 = 0;
        leanh::lean_dec(v_h__3_3510_);
        v_head_3512_ = leanh::lean_ctor_get(v_x_3505_, 0);
        leanh::lean_inc(v_head_3512_);
        v_tail_3513_ = leanh::lean_ctor_get(v_x_3505_, 1);
        leanh::lean_inc(v_tail_3513_);
        leanh::lean_dec_ref_known(v_x_3505_, 2);
        v_zero_3514_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_3515_ = lean_nat_dec_eq(v_x_3506_, v_zero_3514_);
        if v_isZero_3515_ == 1 {
            let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3509_);
            leanh::lean_dec(v_x_3506_);
            v___x_3516_ =
                leanh::lean_apply_3(v_h__1_3508_, v_head_3512_, v_tail_3513_, v_x_3507_);
            return v___x_3516_;
        } else {
            let mut v_one_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_3508_);
            v_one_3517_ = leanh::lean_unsigned_to_nat(1);
            v_n_3518_ = lean_nat_sub(v_x_3506_, v_one_3517_);
            leanh::lean_dec(v_x_3506_);
            v___x_3519_ = leanh::lean_apply_4(
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
    mut v_x_3520_: *mut leanh::LeanObject,
    mut v_x_3521_: *mut leanh::LeanObject,
    mut v_h__1_3522_: *mut leanh::LeanObject,
    mut v_h__2_3523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3520_) == 0 {
        let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3523_);
        v___x_3524_ = leanh::lean_apply_1(v_h__1_3522_, v_x_3521_);
        return v___x_3524_;
    } else {
        let mut v_head_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3522_);
        v_head_3525_ = leanh::lean_ctor_get(v_x_3520_, 0);
        leanh::lean_inc(v_head_3525_);
        v_tail_3526_ = leanh::lean_ctor_get(v_x_3520_, 1);
        leanh::lean_inc(v_tail_3526_);
        leanh::lean_dec_ref_known(v_x_3520_, 2);
        v___x_3527_ =
            leanh::lean_apply_3(v_h__2_3523_, v_head_3525_, v_tail_3526_, v_x_3521_);
        return v___x_3527_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_concat_match__1_splitter(
    mut v_00_u03b1_3528_: *mut leanh::LeanObject,
    mut v_motive_3529_: *mut leanh::LeanObject,
    mut v_x_3530_: *mut leanh::LeanObject,
    mut v_x_3531_: *mut leanh::LeanObject,
    mut v_h__1_3532_: *mut leanh::LeanObject,
    mut v_h__2_3533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3530_) == 0 {
        let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_3533_);
        v___x_3534_ = leanh::lean_apply_1(v_h__1_3532_, v_x_3531_);
        return v___x_3534_;
    } else {
        let mut v_head_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_3532_);
        v_head_3535_ = leanh::lean_ctor_get(v_x_3530_, 0);
        leanh::lean_inc(v_head_3535_);
        v_tail_3536_ = leanh::lean_ctor_get(v_x_3530_, 1);
        leanh::lean_inc(v_tail_3536_);
        leanh::lean_dec_ref_known(v_x_3530_, 2);
        v___x_3537_ =
            leanh::lean_apply_3(v_h__2_3533_, v_head_3535_, v_tail_3536_, v_x_3531_);
        return v___x_3537_;
    }
}
pub unsafe fn l_List_beq___redArg(
    mut v_inst_3538_: *mut leanh::LeanObject,
    mut v_x_3539_: *mut leanh::LeanObject,
    mut v_x_3540_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: u8 = 0;
    let mut v_head_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3539_) == 0 {
                    leanh::lean_dec_ref(v_inst_3538_);
                    if leanh::lean_obj_tag(v_x_3540_) == 0 {
                        v___x_3541_ = 1;
                        return v___x_3541_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_3540_, 2);
                        v___x_3542_ = 0;
                        return v___x_3542_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_3540_) == 0 {
                        leanh::lean_dec_ref_known(v_x_3539_, 2);
                        leanh::lean_dec_ref(v_inst_3538_);
                        v___x_3543_ = 0;
                        return v___x_3543_;
                    } else {
                        v_head_3544_ = leanh::lean_ctor_get(v_x_3539_, 0);
                        leanh::lean_inc(v_head_3544_);
                        v_tail_3545_ = leanh::lean_ctor_get(v_x_3539_, 1);
                        leanh::lean_inc(v_tail_3545_);
                        leanh::lean_dec_ref_known(v_x_3539_, 2);
                        v_head_3546_ = leanh::lean_ctor_get(v_x_3540_, 0);
                        leanh::lean_inc(v_head_3546_);
                        v_tail_3547_ = leanh::lean_ctor_get(v_x_3540_, 1);
                        leanh::lean_inc(v_tail_3547_);
                        leanh::lean_dec_ref_known(v_x_3540_, 2);
                        leanh::lean_inc_ref(v_inst_3538_);
                        v___x_3548_ =
                            leanh::lean_apply_2(v_inst_3538_, v_head_3544_, v_head_3546_);
                        v___x_3549_ = (leanh::lean_unbox(v___x_3548_) as u8);
                        if v___x_3549_ == 0 {
                            leanh::lean_dec(v_tail_3547_);
                            leanh::lean_dec(v_tail_3545_);
                            leanh::lean_dec_ref(v_inst_3538_);
                            v___x_3550_ = (leanh::lean_unbox(v___x_3548_) as u8);
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
    mut v_inst_3552_: *mut leanh::LeanObject,
    mut v_x_3553_: *mut leanh::LeanObject,
    mut v_x_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3555_: u8 = 0;
    let mut v_r_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3555_ = l_List_beq___redArg(v_inst_3552_, v_x_3553_, v_x_3554_);
    v_r_3556_ = leanh::lean_box((v_res_3555_) as usize);
    return v_r_3556_;
}
pub unsafe fn l_List_beq(
    mut v_00_u03b1_3557_: *mut leanh::LeanObject,
    mut v_inst_3558_: *mut leanh::LeanObject,
    mut v_x_3559_: *mut leanh::LeanObject,
    mut v_x_3560_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3561_: u8 = 0;
    v___x_3561_ = l_List_beq___redArg(v_inst_3558_, v_x_3559_, v_x_3560_);
    return v___x_3561_;
}
pub unsafe fn l_List_beq___boxed(
    mut v_00_u03b1_3562_: *mut leanh::LeanObject,
    mut v_inst_3563_: *mut leanh::LeanObject,
    mut v_x_3564_: *mut leanh::LeanObject,
    mut v_x_3565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3566_: u8 = 0;
    let mut v_r_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3566_ = l_List_beq(v_00_u03b1_3562_, v_inst_3563_, v_x_3564_, v_x_3565_);
    v_r_3567_ = leanh::lean_box((v_res_3566_) as usize);
    return v_r_3567_;
}
pub unsafe fn l_List_instBEq___redArg(
    mut v_inst_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ =
        leanh::lean_alloc_closure(l_List_beq___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_3569_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3569_, 1, v_inst_3568_);
    return v___x_3569_;
}
pub unsafe fn l_List_instBEq(
    mut v_00_u03b1_3570_: *mut leanh::LeanObject,
    mut v_inst_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3572_ =
        leanh::lean_alloc_closure(l_List_beq___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_3572_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3572_, 1, v_inst_3571_);
    return v___x_3572_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_beq_match__1_splitter___redArg(
    mut v_x_3573_: *mut leanh::LeanObject,
    mut v_x_3574_: *mut leanh::LeanObject,
    mut v_h__1_3575_: *mut leanh::LeanObject,
    mut v_h__2_3576_: *mut leanh::LeanObject,
    mut v_h__3_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3573_) == 0 {
        leanh::lean_dec(v_h__2_3576_);
        if leanh::lean_obj_tag(v_x_3574_) == 0 {
            let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3577_);
            v___x_3578_ = leanh::lean_box(0);
            v___x_3579_ = leanh::lean_apply_1(v_h__1_3575_, v___x_3578_);
            return v___x_3579_;
        } else {
            let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_3575_);
            v___x_3580_ = leanh::lean_apply_4(
                v_h__3_3577_,
                v_x_3573_,
                v_x_3574_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_3580_;
        }
    } else {
        leanh::lean_dec(v_h__1_3575_);
        if leanh::lean_obj_tag(v_x_3574_) == 0 {
            let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3576_);
            v___x_3581_ = leanh::lean_apply_4(
                v_h__3_3577_,
                v_x_3573_,
                v_x_3574_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_3581_;
        } else {
            let mut v_head_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3577_);
            v_head_3582_ = leanh::lean_ctor_get(v_x_3573_, 0);
            leanh::lean_inc(v_head_3582_);
            v_tail_3583_ = leanh::lean_ctor_get(v_x_3573_, 1);
            leanh::lean_inc(v_tail_3583_);
            leanh::lean_dec_ref_known(v_x_3573_, 2);
            v_head_3584_ = leanh::lean_ctor_get(v_x_3574_, 0);
            leanh::lean_inc(v_head_3584_);
            v_tail_3585_ = leanh::lean_ctor_get(v_x_3574_, 1);
            leanh::lean_inc(v_tail_3585_);
            leanh::lean_dec_ref_known(v_x_3574_, 2);
            v___x_3586_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_3587_: *mut leanh::LeanObject,
    mut v_motive_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
    mut v_h__1_3591_: *mut leanh::LeanObject,
    mut v_h__2_3592_: *mut leanh::LeanObject,
    mut v_h__3_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3589_) == 0 {
        leanh::lean_dec(v_h__2_3592_);
        if leanh::lean_obj_tag(v_x_3590_) == 0 {
            let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3593_);
            v___x_3594_ = leanh::lean_box(0);
            v___x_3595_ = leanh::lean_apply_1(v_h__1_3591_, v___x_3594_);
            return v___x_3595_;
        } else {
            let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_3591_);
            v___x_3596_ = leanh::lean_apply_4(
                v_h__3_3593_,
                v_x_3589_,
                v_x_3590_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_3596_;
        }
    } else {
        leanh::lean_dec(v_h__1_3591_);
        if leanh::lean_obj_tag(v_x_3590_) == 0 {
            let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3592_);
            v___x_3597_ = leanh::lean_apply_4(
                v_h__3_3593_,
                v_x_3589_,
                v_x_3590_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_3597_;
        } else {
            let mut v_head_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3593_);
            v_head_3598_ = leanh::lean_ctor_get(v_x_3589_, 0);
            leanh::lean_inc(v_head_3598_);
            v_tail_3599_ = leanh::lean_ctor_get(v_x_3589_, 1);
            leanh::lean_inc(v_tail_3599_);
            leanh::lean_dec_ref_known(v_x_3589_, 2);
            v_head_3600_ = leanh::lean_ctor_get(v_x_3590_, 0);
            leanh::lean_inc(v_head_3600_);
            v_tail_3601_ = leanh::lean_ctor_get(v_x_3590_, 1);
            leanh::lean_inc(v_tail_3601_);
            leanh::lean_dec_ref_known(v_x_3590_, 2);
            v___x_3602_ = leanh::lean_apply_4(
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
    mut v_x_3603_: *mut leanh::LeanObject,
    mut v_x_3604_: *mut leanh::LeanObject,
    mut v_x_3605_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3606_: u8 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: u8 = 0;
    let mut v_head_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: u8 = 0;
    let mut v___x_3615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3603_) == 0 {
                    leanh::lean_dec_ref(v_x_3605_);
                    if leanh::lean_obj_tag(v_x_3604_) == 0 {
                        v___x_3606_ = 1;
                        return v___x_3606_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_3604_, 2);
                        v___x_3607_ = 0;
                        return v___x_3607_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_3604_) == 0 {
                        leanh::lean_dec_ref_known(v_x_3603_, 2);
                        leanh::lean_dec_ref(v_x_3605_);
                        v___x_3608_ = 0;
                        return v___x_3608_;
                    } else {
                        v_head_3609_ = leanh::lean_ctor_get(v_x_3603_, 0);
                        leanh::lean_inc(v_head_3609_);
                        v_tail_3610_ = leanh::lean_ctor_get(v_x_3603_, 1);
                        leanh::lean_inc(v_tail_3610_);
                        leanh::lean_dec_ref_known(v_x_3603_, 2);
                        v_head_3611_ = leanh::lean_ctor_get(v_x_3604_, 0);
                        leanh::lean_inc(v_head_3611_);
                        v_tail_3612_ = leanh::lean_ctor_get(v_x_3604_, 1);
                        leanh::lean_inc(v_tail_3612_);
                        leanh::lean_dec_ref_known(v_x_3604_, 2);
                        leanh::lean_inc_ref(v_x_3605_);
                        v___x_3613_ =
                            leanh::lean_apply_2(v_x_3605_, v_head_3609_, v_head_3611_);
                        v___x_3614_ = (leanh::lean_unbox(v___x_3613_) as u8);
                        if v___x_3614_ == 0 {
                            leanh::lean_dec(v_tail_3612_);
                            leanh::lean_dec(v_tail_3610_);
                            leanh::lean_dec_ref(v_x_3605_);
                            v___x_3615_ = (leanh::lean_unbox(v___x_3613_) as u8);
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
    mut v_x_3617_: *mut leanh::LeanObject,
    mut v_x_3618_: *mut leanh::LeanObject,
    mut v_x_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3620_: u8 = 0;
    let mut v_r_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3620_ = l_List_isEqv___redArg(v_x_3617_, v_x_3618_, v_x_3619_);
    v_r_3621_ = leanh::lean_box((v_res_3620_) as usize);
    return v_r_3621_;
}
pub unsafe fn l_List_isEqv(
    mut v_00_u03b1_3622_: *mut leanh::LeanObject,
    mut v_x_3623_: *mut leanh::LeanObject,
    mut v_x_3624_: *mut leanh::LeanObject,
    mut v_x_3625_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3626_: u8 = 0;
    v___x_3626_ = l_List_isEqv___redArg(v_x_3623_, v_x_3624_, v_x_3625_);
    return v___x_3626_;
}
pub unsafe fn l_List_isEqv___boxed(
    mut v_00_u03b1_3627_: *mut leanh::LeanObject,
    mut v_x_3628_: *mut leanh::LeanObject,
    mut v_x_3629_: *mut leanh::LeanObject,
    mut v_x_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3631_: u8 = 0;
    let mut v_r_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_List_isEqv(v_00_u03b1_3627_, v_x_3628_, v_x_3629_, v_x_3630_);
    v_r_3632_ = leanh::lean_box((v_res_3631_) as usize);
    return v_r_3632_;
}
pub unsafe fn l_List_decidableLex___redArg(
    mut v_inst_3633_: *mut leanh::LeanObject,
    mut v_h_3634_: *mut leanh::LeanObject,
    mut v_x_3635_: *mut leanh::LeanObject,
    mut v_x_3636_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3635_) == 0 {
        leanh::lean_dec_ref(v_h_3634_);
        leanh::lean_dec_ref(v_inst_3633_);
        if leanh::lean_obj_tag(v_x_3636_) == 0 {
            let mut v___x_3637_: u8 = 0;
            v___x_3637_ = 0;
            return v___x_3637_;
        } else {
            let mut v___x_3638_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_3636_, 2);
            v___x_3638_ = 1;
            return v___x_3638_;
        }
    } else {
        let mut v_head_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: u8 = 0;
        v_head_3639_ = leanh::lean_ctor_get(v_x_3635_, 0);
        leanh::lean_inc(v_head_3639_);
        v_tail_3640_ = leanh::lean_ctor_get(v_x_3635_, 1);
        leanh::lean_inc(v_tail_3640_);
        leanh::lean_dec_ref_known(v_x_3635_, 2);
        v___x_3641_ = 0;
        if leanh::lean_obj_tag(v_x_3636_) == 0 {
            leanh::lean_dec(v_tail_3640_);
            leanh::lean_dec(v_head_3639_);
            leanh::lean_dec_ref(v_h_3634_);
            leanh::lean_dec_ref(v_inst_3633_);
            return v___x_3641_;
        } else {
            let mut v_head_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3646_: u8 = 0;
            v_head_3642_ = leanh::lean_ctor_get(v_x_3636_, 0);
            leanh::lean_inc_n(v_head_3642_, 2);
            v_tail_3643_ = leanh::lean_ctor_get(v_x_3636_, 1);
            leanh::lean_inc(v_tail_3643_);
            leanh::lean_dec_ref_known(v_x_3636_, 2);
            leanh::lean_inc_ref(v_inst_3633_);
            leanh::lean_inc(v_head_3639_);
            v___x_3644_ = leanh::lean_apply_2(v_inst_3633_, v_head_3639_, v_head_3642_);
            leanh::lean_inc_ref(v_h_3634_);
            v___x_3645_ = leanh::lean_apply_2(v_h_3634_, v_head_3639_, v_head_3642_);
            v___x_3646_ = (leanh::lean_unbox(v___x_3645_) as u8);
            if v___x_3646_ == 0 {
                let mut v___x_3647_: u8 = 0;
                v___x_3647_ = (leanh::lean_unbox(v___x_3644_) as u8);
                if v___x_3647_ == 0 {
                    leanh::lean_dec(v_tail_3643_);
                    leanh::lean_dec(v_tail_3640_);
                    leanh::lean_dec_ref(v_h_3634_);
                    leanh::lean_dec_ref(v_inst_3633_);
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
                leanh::lean_dec(v_tail_3643_);
                leanh::lean_dec(v_tail_3640_);
                leanh::lean_dec_ref(v_h_3634_);
                leanh::lean_dec_ref(v_inst_3633_);
                v___x_3649_ = (leanh::lean_unbox(v___x_3645_) as u8);
                return v___x_3649_;
            }
        }
    }
}
pub unsafe fn l_List_decidableLex___redArg___boxed(
    mut v_inst_3650_: *mut leanh::LeanObject,
    mut v_h_3651_: *mut leanh::LeanObject,
    mut v_x_3652_: *mut leanh::LeanObject,
    mut v_x_3653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3654_: u8 = 0;
    let mut v_r_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3654_ = l_List_decidableLex___redArg(v_inst_3650_, v_h_3651_, v_x_3652_, v_x_3653_);
    v_r_3655_ = leanh::lean_box((v_res_3654_) as usize);
    return v_r_3655_;
}
pub unsafe fn l_List_decidableLex(
    mut v_00_u03b1_3656_: *mut leanh::LeanObject,
    mut v_inst_3657_: *mut leanh::LeanObject,
    mut v_r_3658_: *mut leanh::LeanObject,
    mut v_h_3659_: *mut leanh::LeanObject,
    mut v_x_3660_: *mut leanh::LeanObject,
    mut v_x_3661_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3662_: u8 = 0;
    v___x_3662_ = l_List_decidableLex___redArg(v_inst_3657_, v_h_3659_, v_x_3660_, v_x_3661_);
    return v___x_3662_;
}
pub unsafe fn l_List_decidableLex___boxed(
    mut v_00_u03b1_3663_: *mut leanh::LeanObject,
    mut v_inst_3664_: *mut leanh::LeanObject,
    mut v_r_3665_: *mut leanh::LeanObject,
    mut v_h_3666_: *mut leanh::LeanObject,
    mut v_x_3667_: *mut leanh::LeanObject,
    mut v_x_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3669_: u8 = 0;
    let mut v_r_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_List_decidableLex(
        v_00_u03b1_3663_,
        v_inst_3664_,
        v_r_3665_,
        v_h_3666_,
        v_x_3667_,
        v_x_3668_,
    );
    v_r_3670_ = leanh::lean_box((v_res_3669_) as usize);
    return v_r_3670_;
}
pub unsafe fn l_List_instLT(
    mut v_00_u03b1_3671_: *mut leanh::LeanObject,
    mut v_inst_3672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = leanh::lean_box(0);
    return v___x_3673_;
}
pub unsafe fn l_List_decidableLT___redArg(
    mut v_inst_3674_: *mut leanh::LeanObject,
    mut v_inst_3675_: *mut leanh::LeanObject,
    mut v_l_u2081_3676_: *mut leanh::LeanObject,
    mut v_l_u2082_3677_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3678_: u8 = 0;
    v___x_3678_ =
        l_List_decidableLex___redArg(v_inst_3674_, v_inst_3675_, v_l_u2081_3676_, v_l_u2082_3677_);
    return v___x_3678_;
}
pub unsafe fn l_List_decidableLT___redArg___boxed(
    mut v_inst_3679_: *mut leanh::LeanObject,
    mut v_inst_3680_: *mut leanh::LeanObject,
    mut v_l_u2081_3681_: *mut leanh::LeanObject,
    mut v_l_u2082_3682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3683_: u8 = 0;
    let mut v_r_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3683_ =
        l_List_decidableLT___redArg(v_inst_3679_, v_inst_3680_, v_l_u2081_3681_, v_l_u2082_3682_);
    v_r_3684_ = leanh::lean_box((v_res_3683_) as usize);
    return v_r_3684_;
}
pub unsafe fn l_List_decidableLT(
    mut v_00_u03b1_3685_: *mut leanh::LeanObject,
    mut v_inst_3686_: *mut leanh::LeanObject,
    mut v_inst_3687_: *mut leanh::LeanObject,
    mut v_inst_3688_: *mut leanh::LeanObject,
    mut v_l_u2081_3689_: *mut leanh::LeanObject,
    mut v_l_u2082_3690_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3691_: u8 = 0;
    v___x_3691_ =
        l_List_decidableLex___redArg(v_inst_3686_, v_inst_3688_, v_l_u2081_3689_, v_l_u2082_3690_);
    return v___x_3691_;
}
pub unsafe fn l_List_decidableLT___boxed(
    mut v_00_u03b1_3692_: *mut leanh::LeanObject,
    mut v_inst_3693_: *mut leanh::LeanObject,
    mut v_inst_3694_: *mut leanh::LeanObject,
    mut v_inst_3695_: *mut leanh::LeanObject,
    mut v_l_u2081_3696_: *mut leanh::LeanObject,
    mut v_l_u2082_3697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3698_: u8 = 0;
    let mut v_r_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_List_decidableLT(
        v_00_u03b1_3692_,
        v_inst_3693_,
        v_inst_3694_,
        v_inst_3695_,
        v_l_u2081_3696_,
        v_l_u2082_3697_,
    );
    v_r_3699_ = leanh::lean_box((v_res_3698_) as usize);
    return v_r_3699_;
}
pub unsafe fn l_List_instLE(
    mut v_00_u03b1_3700_: *mut leanh::LeanObject,
    mut v_inst_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = leanh::lean_box(0);
    return v___x_3702_;
}
pub unsafe fn l_List_decidableLE___redArg(
    mut v_inst_3703_: *mut leanh::LeanObject,
    mut v_inst_3704_: *mut leanh::LeanObject,
    mut v_l_u2081_3705_: *mut leanh::LeanObject,
    mut v_l_u2082_3706_: *mut leanh::LeanObject,
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
    mut v_inst_3710_: *mut leanh::LeanObject,
    mut v_inst_3711_: *mut leanh::LeanObject,
    mut v_l_u2081_3712_: *mut leanh::LeanObject,
    mut v_l_u2082_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3714_: u8 = 0;
    let mut v_r_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3714_ =
        l_List_decidableLE___redArg(v_inst_3710_, v_inst_3711_, v_l_u2081_3712_, v_l_u2082_3713_);
    v_r_3715_ = leanh::lean_box((v_res_3714_) as usize);
    return v_r_3715_;
}
pub unsafe fn l_List_decidableLE(
    mut v_00_u03b1_3716_: *mut leanh::LeanObject,
    mut v_inst_3717_: *mut leanh::LeanObject,
    mut v_inst_3718_: *mut leanh::LeanObject,
    mut v_inst_3719_: *mut leanh::LeanObject,
    mut v_l_u2081_3720_: *mut leanh::LeanObject,
    mut v_l_u2082_3721_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3722_: u8 = 0;
    v___x_3722_ =
        l_List_decidableLE___redArg(v_inst_3717_, v_inst_3719_, v_l_u2081_3720_, v_l_u2082_3721_);
    return v___x_3722_;
}
pub unsafe fn l_List_decidableLE___boxed(
    mut v_00_u03b1_3723_: *mut leanh::LeanObject,
    mut v_inst_3724_: *mut leanh::LeanObject,
    mut v_inst_3725_: *mut leanh::LeanObject,
    mut v_inst_3726_: *mut leanh::LeanObject,
    mut v_l_u2081_3727_: *mut leanh::LeanObject,
    mut v_l_u2082_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3729_: u8 = 0;
    let mut v_r_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_List_decidableLE(
        v_00_u03b1_3723_,
        v_inst_3724_,
        v_inst_3725_,
        v_inst_3726_,
        v_l_u2081_3727_,
        v_l_u2082_3728_,
    );
    v_r_3730_ = leanh::lean_box((v_res_3729_) as usize);
    return v_r_3730_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_List_lex___auto__1___closed__10;
    v___x_3758_ = l_Lean_mkAtom(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__12_once),
        _init_l_List_lex___auto__1___closed__12,
    );
    v___x_3760_ = l_List_lex___auto__1___closed__5;
    v___x_3761_ = lean_array_push(v___x_3760_, v___x_3759_);
    return v___x_3761_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_List_lex___auto__1___closed__19;
    v___x_3777_ = l_Lean_mkAtom(v___x_3776_);
    return v___x_3777_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3778_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__20_once),
        _init_l_List_lex___auto__1___closed__20,
    );
    v___x_3779_ = l_List_lex___auto__1___closed__5;
    v___x_3780_ = lean_array_push(v___x_3779_, v___x_3778_);
    return v___x_3780_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_List_lex___auto__1___closed__24;
    v___x_3786_ = lean_string_utf8_byte_size(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__25_once),
        _init_l_List_lex___auto__1___closed__25,
    );
    v___x_3788_ = leanh::lean_unsigned_to_nat(0);
    v___x_3789_ = l_List_lex___auto__1___closed__24;
    v___x_3790_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    leanh::lean_ctor_set(v___x_3790_, 1, v___x_3788_);
    leanh::lean_ctor_set(v___x_3790_, 2, v___x_3787_);
    return v___x_3790_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = leanh::lean_box(0);
    v___x_3792_ = leanh::lean_box(0);
    v___x_3793_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__26_once),
        _init_l_List_lex___auto__1___closed__26,
    );
    v___x_3794_ = leanh::lean_box(2);
    v___x_3795_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3795_, 0, v___x_3794_);
    leanh::lean_ctor_set(v___x_3795_, 1, v___x_3793_);
    leanh::lean_ctor_set(v___x_3795_, 2, v___x_3792_);
    leanh::lean_ctor_set(v___x_3795_, 3, v___x_3791_);
    return v___x_3795_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3796_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__27_once),
        _init_l_List_lex___auto__1___closed__27,
    );
    v___x_3797_ = l_List_lex___auto__1___closed__5;
    v___x_3798_ = lean_array_push(v___x_3797_, v___x_3796_);
    return v___x_3798_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3799_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__28_once),
        _init_l_List_lex___auto__1___closed__28,
    );
    v___x_3800_ = l_List_lex___auto__1___closed__23;
    v___x_3801_ = leanh::lean_box(2);
    v___x_3802_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
    leanh::lean_ctor_set(v___x_3802_, 1, v___x_3800_);
    leanh::lean_ctor_set(v___x_3802_, 2, v___x_3799_);
    return v___x_3802_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29_once),
        _init_l_List_lex___auto__1___closed__29,
    );
    v___x_3804_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__21_once),
        _init_l_List_lex___auto__1___closed__21,
    );
    v___x_3805_ = lean_array_push(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__31() -> *mut leanh::LeanObject {
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3806_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__30_once),
        _init_l_List_lex___auto__1___closed__30,
    );
    v___x_3807_ = l_List_lex___auto__1___closed__18;
    v___x_3808_ = leanh::lean_box(2);
    v___x_3809_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3809_, 0, v___x_3808_);
    leanh::lean_ctor_set(v___x_3809_, 1, v___x_3807_);
    leanh::lean_ctor_set(v___x_3809_, 2, v___x_3806_);
    return v___x_3809_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__31_once),
        _init_l_List_lex___auto__1___closed__31,
    );
    v___x_3811_ = l_List_lex___auto__1___closed__5;
    v___x_3812_ = lean_array_push(v___x_3811_, v___x_3810_);
    return v___x_3812_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__38() -> *mut leanh::LeanObject {
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_List_lex___auto__1___closed__37;
    v___x_3824_ = l_Lean_mkAtom(v___x_3823_);
    return v___x_3824_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__39() -> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__38_once),
        _init_l_List_lex___auto__1___closed__38,
    );
    v___x_3826_ = l_List_lex___auto__1___closed__5;
    v___x_3827_ = lean_array_push(v___x_3826_, v___x_3825_);
    return v___x_3827_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__40() -> *mut leanh::LeanObject {
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__29_once),
        _init_l_List_lex___auto__1___closed__29,
    );
    v___x_3829_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__39_once),
        _init_l_List_lex___auto__1___closed__39,
    );
    v___x_3830_ = lean_array_push(v___x_3829_, v___x_3828_);
    return v___x_3830_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__41() -> *mut leanh::LeanObject {
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__40_once),
        _init_l_List_lex___auto__1___closed__40,
    );
    v___x_3832_ = l_List_lex___auto__1___closed__36;
    v___x_3833_ = leanh::lean_box(2);
    v___x_3834_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3834_, 0, v___x_3833_);
    leanh::lean_ctor_set(v___x_3834_, 1, v___x_3832_);
    leanh::lean_ctor_set(v___x_3834_, 2, v___x_3831_);
    return v___x_3834_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41_once),
        _init_l_List_lex___auto__1___closed__41,
    );
    v___x_3836_ = l_List_lex___auto__1___closed__5;
    v___x_3837_ = lean_array_push(v___x_3836_, v___x_3835_);
    return v___x_3837_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__44() -> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_List_lex___auto__1___closed__43;
    v___x_3840_ = l_Lean_mkAtom(v___x_3839_);
    return v___x_3840_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__44_once),
        _init_l_List_lex___auto__1___closed__44,
    );
    v___x_3842_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__42_once),
        _init_l_List_lex___auto__1___closed__42,
    );
    v___x_3843_ = lean_array_push(v___x_3842_, v___x_3841_);
    return v___x_3843_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__46() -> *mut leanh::LeanObject {
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__41_once),
        _init_l_List_lex___auto__1___closed__41,
    );
    v___x_3845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__45_once),
        _init_l_List_lex___auto__1___closed__45,
    );
    v___x_3846_ = lean_array_push(v___x_3845_, v___x_3844_);
    return v___x_3846_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__47() -> *mut leanh::LeanObject {
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__46_once),
        _init_l_List_lex___auto__1___closed__46,
    );
    v___x_3848_ = l_List_lex___auto__1___closed__34;
    v___x_3849_ = leanh::lean_box(2);
    v___x_3850_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3850_, 0, v___x_3849_);
    leanh::lean_ctor_set(v___x_3850_, 1, v___x_3848_);
    leanh::lean_ctor_set(v___x_3850_, 2, v___x_3847_);
    return v___x_3850_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__48() -> *mut leanh::LeanObject {
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__47_once),
        _init_l_List_lex___auto__1___closed__47,
    );
    v___x_3852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__32_once),
        _init_l_List_lex___auto__1___closed__32,
    );
    v___x_3853_ = lean_array_push(v___x_3852_, v___x_3851_);
    return v___x_3853_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__50() -> *mut leanh::LeanObject {
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ = l_List_lex___auto__1___closed__49;
    v___x_3856_ = l_Lean_mkAtom(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__51() -> *mut leanh::LeanObject {
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__50_once),
        _init_l_List_lex___auto__1___closed__50,
    );
    v___x_3858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__48_once),
        _init_l_List_lex___auto__1___closed__48,
    );
    v___x_3859_ = lean_array_push(v___x_3858_, v___x_3857_);
    return v___x_3859_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__52() -> *mut leanh::LeanObject {
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__51_once),
        _init_l_List_lex___auto__1___closed__51,
    );
    v___x_3861_ = l_List_lex___auto__1___closed__16;
    v___x_3862_ = leanh::lean_box(2);
    v___x_3863_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3863_, 0, v___x_3862_);
    leanh::lean_ctor_set(v___x_3863_, 1, v___x_3861_);
    leanh::lean_ctor_set(v___x_3863_, 2, v___x_3860_);
    return v___x_3863_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__53() -> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__52_once),
        _init_l_List_lex___auto__1___closed__52,
    );
    v___x_3865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__13_once),
        _init_l_List_lex___auto__1___closed__13,
    );
    v___x_3866_ = lean_array_push(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__54() -> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__53_once),
        _init_l_List_lex___auto__1___closed__53,
    );
    v___x_3868_ = l_List_lex___auto__1___closed__11;
    v___x_3869_ = leanh::lean_box(2);
    v___x_3870_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3870_, 0, v___x_3869_);
    leanh::lean_ctor_set(v___x_3870_, 1, v___x_3868_);
    leanh::lean_ctor_set(v___x_3870_, 2, v___x_3867_);
    return v___x_3870_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__55() -> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__54_once),
        _init_l_List_lex___auto__1___closed__54,
    );
    v___x_3872_ = l_List_lex___auto__1___closed__5;
    v___x_3873_ = lean_array_push(v___x_3872_, v___x_3871_);
    return v___x_3873_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__56() -> *mut leanh::LeanObject {
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__55_once),
        _init_l_List_lex___auto__1___closed__55,
    );
    v___x_3875_ = l_List_lex___auto__1___closed__9;
    v___x_3876_ = leanh::lean_box(2);
    v___x_3877_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3876_);
    leanh::lean_ctor_set(v___x_3877_, 1, v___x_3875_);
    leanh::lean_ctor_set(v___x_3877_, 2, v___x_3874_);
    return v___x_3877_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__57() -> *mut leanh::LeanObject {
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__56_once),
        _init_l_List_lex___auto__1___closed__56,
    );
    v___x_3879_ = l_List_lex___auto__1___closed__5;
    v___x_3880_ = lean_array_push(v___x_3879_, v___x_3878_);
    return v___x_3880_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__58() -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__57_once),
        _init_l_List_lex___auto__1___closed__57,
    );
    v___x_3882_ = l_List_lex___auto__1___closed__7;
    v___x_3883_ = leanh::lean_box(2);
    v___x_3884_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3884_, 0, v___x_3883_);
    leanh::lean_ctor_set(v___x_3884_, 1, v___x_3882_);
    leanh::lean_ctor_set(v___x_3884_, 2, v___x_3881_);
    return v___x_3884_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__59() -> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__58_once),
        _init_l_List_lex___auto__1___closed__58,
    );
    v___x_3886_ = l_List_lex___auto__1___closed__5;
    v___x_3887_ = lean_array_push(v___x_3886_, v___x_3885_);
    return v___x_3887_;
}
pub unsafe fn _init_l_List_lex___auto__1___closed__60() -> *mut leanh::LeanObject {
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3888_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__59),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__59_once),
        _init_l_List_lex___auto__1___closed__59,
    );
    v___x_3889_ = l_List_lex___auto__1___closed__4;
    v___x_3890_ = leanh::lean_box(2);
    v___x_3891_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3891_, 0, v___x_3890_);
    leanh::lean_ctor_set(v___x_3891_, 1, v___x_3889_);
    leanh::lean_ctor_set(v___x_3891_, 2, v___x_3888_);
    return v___x_3891_;
}
pub unsafe fn _init_l_List_lex___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__60),
        core::ptr::addr_of_mut!(l_List_lex___auto__1___closed__60_once),
        _init_l_List_lex___auto__1___closed__60,
    );
    return v___x_3892_;
}
pub unsafe fn l_List_lex___redArg(
    mut v_inst_3893_: *mut leanh::LeanObject,
    mut v_l_u2081_3894_: *mut leanh::LeanObject,
    mut v_l_u2082_3895_: *mut leanh::LeanObject,
    mut v_lt_3896_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: u8 = 0;
    let mut v_head_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_u2081_3894_) == 0 {
                    leanh::lean_dec_ref(v_lt_3896_);
                    leanh::lean_dec_ref(v_inst_3893_);
                    if leanh::lean_obj_tag(v_l_u2082_3895_) == 0 {
                        v___x_3897_ = 0;
                        return v___x_3897_;
                    } else {
                        leanh::lean_dec_ref_known(v_l_u2082_3895_, 2);
                        v___x_3898_ = 1;
                        return v___x_3898_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_u2082_3895_) == 0 {
                        leanh::lean_dec_ref_known(v_l_u2081_3894_, 2);
                        leanh::lean_dec_ref(v_lt_3896_);
                        leanh::lean_dec_ref(v_inst_3893_);
                        v___x_3899_ = 0;
                        return v___x_3899_;
                    } else {
                        v_head_3900_ = leanh::lean_ctor_get(v_l_u2081_3894_, 0);
                        leanh::lean_inc_n(v_head_3900_, 2);
                        v_tail_3901_ = leanh::lean_ctor_get(v_l_u2081_3894_, 1);
                        leanh::lean_inc(v_tail_3901_);
                        leanh::lean_dec_ref_known(v_l_u2081_3894_, 2);
                        v_head_3902_ = leanh::lean_ctor_get(v_l_u2082_3895_, 0);
                        leanh::lean_inc_n(v_head_3902_, 2);
                        v_tail_3903_ = leanh::lean_ctor_get(v_l_u2082_3895_, 1);
                        leanh::lean_inc(v_tail_3903_);
                        leanh::lean_dec_ref_known(v_l_u2082_3895_, 2);
                        leanh::lean_inc_ref(v_lt_3896_);
                        v___x_3904_ =
                            leanh::lean_apply_2(v_lt_3896_, v_head_3900_, v_head_3902_);
                        v___x_3905_ = (leanh::lean_unbox(v___x_3904_) as u8);
                        if v___x_3905_ == 0 {
                            leanh::lean_inc_ref(v_inst_3893_);
                            v___x_3906_ = leanh::lean_apply_2(
                                v_inst_3893_,
                                v_head_3900_,
                                v_head_3902_,
                            );
                            v___x_3907_ = (leanh::lean_unbox(v___x_3906_) as u8);
                            if v___x_3907_ == 0 {
                                leanh::lean_dec(v_tail_3903_);
                                leanh::lean_dec(v_tail_3901_);
                                leanh::lean_dec_ref(v_lt_3896_);
                                leanh::lean_dec_ref(v_inst_3893_);
                                v___x_3908_ = (leanh::lean_unbox(v___x_3906_) as u8);
                                return v___x_3908_;
                            } else {
                                v_l_u2081_3894_ = v_tail_3901_;
                                v_l_u2082_3895_ = v_tail_3903_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_tail_3903_);
                            leanh::lean_dec(v_head_3902_);
                            leanh::lean_dec(v_tail_3901_);
                            leanh::lean_dec(v_head_3900_);
                            leanh::lean_dec_ref(v_lt_3896_);
                            leanh::lean_dec_ref(v_inst_3893_);
                            v___x_3910_ = (leanh::lean_unbox(v___x_3904_) as u8);
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
    mut v_inst_3911_: *mut leanh::LeanObject,
    mut v_l_u2081_3912_: *mut leanh::LeanObject,
    mut v_l_u2082_3913_: *mut leanh::LeanObject,
    mut v_lt_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3915_: u8 = 0;
    let mut v_r_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3915_ = l_List_lex___redArg(v_inst_3911_, v_l_u2081_3912_, v_l_u2082_3913_, v_lt_3914_);
    v_r_3916_ = leanh::lean_box((v_res_3915_) as usize);
    return v_r_3916_;
}
pub unsafe fn l_List_lex(
    mut v_00_u03b1_3917_: *mut leanh::LeanObject,
    mut v_inst_3918_: *mut leanh::LeanObject,
    mut v_l_u2081_3919_: *mut leanh::LeanObject,
    mut v_l_u2082_3920_: *mut leanh::LeanObject,
    mut v_lt_3921_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3922_: u8 = 0;
    v___x_3922_ = l_List_lex___redArg(v_inst_3918_, v_l_u2081_3919_, v_l_u2082_3920_, v_lt_3921_);
    return v___x_3922_;
}
pub unsafe fn l_List_lex___boxed(
    mut v_00_u03b1_3923_: *mut leanh::LeanObject,
    mut v_inst_3924_: *mut leanh::LeanObject,
    mut v_l_u2081_3925_: *mut leanh::LeanObject,
    mut v_l_u2082_3926_: *mut leanh::LeanObject,
    mut v_lt_3927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3928_: u8 = 0;
    let mut v_r_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3928_ = l_List_lex(
        v_00_u03b1_3923_,
        v_inst_3924_,
        v_l_u2081_3925_,
        v_l_u2082_3926_,
        v_lt_3927_,
    );
    v_r_3929_ = leanh::lean_box((v_res_3928_) as usize);
    return v_r_3929_;
}
pub unsafe fn l_List_getLast___redArg(
    mut v_x_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tail_3931_ = leanh::lean_ctor_get(v_x_3930_, 1);
                if leanh::lean_obj_tag(v_tail_3931_) == 0 {
                    v_head_3932_ = leanh::lean_ctor_get(v_x_3930_, 0);
                    leanh::lean_inc(v_head_3932_);
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
    mut v_x_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_List_getLast___redArg(v_x_3934_);
    leanh::lean_dec(v_x_3934_);
    return v_res_3935_;
}
pub unsafe fn l_List_getLast(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_x_3937_: *mut leanh::LeanObject,
    mut v_x_3938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_List_getLast___redArg(v_x_3937_);
    return v___x_3939_;
}
pub unsafe fn l_List_getLast___boxed(
    mut v_00_u03b1_3940_: *mut leanh::LeanObject,
    mut v_x_3941_: *mut leanh::LeanObject,
    mut v_x_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_List_getLast(v_00_u03b1_3940_, v_x_3941_, v_x_3942_);
    leanh::lean_dec(v_x_3941_);
    return v_res_3943_;
}
pub unsafe fn l_List_getLast_x3f___redArg(
    mut v_x_3944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3944_) == 0 {
        let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3945_ = leanh::lean_box(0);
        return v___x_3945_;
    } else {
        let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3946_ = l_List_getLast___redArg(v_x_3944_);
        v___x_3947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3947_, 0, v___x_3946_);
        return v___x_3947_;
    }
}
pub unsafe fn l_List_getLast_x3f___redArg___boxed(
    mut v_x_3948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3949_ = l_List_getLast_x3f___redArg(v_x_3948_);
    leanh::lean_dec(v_x_3948_);
    return v_res_3949_;
}
pub unsafe fn l_List_getLast_x3f(
    mut v_00_u03b1_3950_: *mut leanh::LeanObject,
    mut v_x_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_List_getLast_x3f___redArg(v_x_3951_);
    return v___x_3952_;
}
pub unsafe fn l_List_getLast_x3f___boxed(
    mut v_00_u03b1_3953_: *mut leanh::LeanObject,
    mut v_x_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l_List_getLast_x3f(v_00_u03b1_3953_, v_x_3954_);
    leanh::lean_dec(v_x_3954_);
    return v_res_3955_;
}
pub unsafe fn l_List_getLastD___redArg(
    mut v_x_3956_: *mut leanh::LeanObject,
    mut v_x_3957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3956_) == 0 {
        leanh::lean_inc(v_x_3957_);
        return v_x_3957_;
    } else {
        let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3958_ = l_List_getLast___redArg(v_x_3956_);
        return v___x_3958_;
    }
}
pub unsafe fn l_List_getLastD___redArg___boxed(
    mut v_x_3959_: *mut leanh::LeanObject,
    mut v_x_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_List_getLastD___redArg(v_x_3959_, v_x_3960_);
    leanh::lean_dec(v_x_3960_);
    leanh::lean_dec(v_x_3959_);
    return v_res_3961_;
}
pub unsafe fn l_List_getLastD(
    mut v_00_u03b1_3962_: *mut leanh::LeanObject,
    mut v_x_3963_: *mut leanh::LeanObject,
    mut v_x_3964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3965_ = l_List_getLastD___redArg(v_x_3963_, v_x_3964_);
    return v___x_3965_;
}
pub unsafe fn l_List_getLastD___boxed(
    mut v_00_u03b1_3966_: *mut leanh::LeanObject,
    mut v_x_3967_: *mut leanh::LeanObject,
    mut v_x_3968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_List_getLastD(v_00_u03b1_3966_, v_x_3967_, v_x_3968_);
    leanh::lean_dec(v_x_3968_);
    leanh::lean_dec(v_x_3967_);
    return v_res_3969_;
}
pub unsafe fn l_List_head___redArg(
    mut v_x_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_3971_ = leanh::lean_ctor_get(v_x_3970_, 0);
    leanh::lean_inc(v_head_3971_);
    return v_head_3971_;
}
pub unsafe fn l_List_head___redArg___boxed(
    mut v_x_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_List_head___redArg(v_x_3972_);
    leanh::lean_dec(v_x_3972_);
    return v_res_3973_;
}
pub unsafe fn l_List_head(
    mut v_00_u03b1_3974_: *mut leanh::LeanObject,
    mut v_x_3975_: *mut leanh::LeanObject,
    mut v_x_3976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_3977_ = leanh::lean_ctor_get(v_x_3975_, 0);
    leanh::lean_inc(v_head_3977_);
    return v_head_3977_;
}
pub unsafe fn l_List_head___boxed(
    mut v_00_u03b1_3978_: *mut leanh::LeanObject,
    mut v_x_3979_: *mut leanh::LeanObject,
    mut v_x_3980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3981_ = l_List_head(v_00_u03b1_3978_, v_x_3979_, v_x_3980_);
    leanh::lean_dec(v_x_3979_);
    return v_res_3981_;
}
pub unsafe fn l_List_head_x3f___redArg(
    mut v_x_3982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3982_) == 0 {
        let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3983_ = leanh::lean_box(0);
        return v___x_3983_;
    } else {
        let mut v_head_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_3984_ = leanh::lean_ctor_get(v_x_3982_, 0);
        leanh::lean_inc(v_head_3984_);
        v___x_3985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3985_, 0, v_head_3984_);
        return v___x_3985_;
    }
}
pub unsafe fn l_List_head_x3f___redArg___boxed(
    mut v_x_3986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_List_head_x3f___redArg(v_x_3986_);
    leanh::lean_dec(v_x_3986_);
    return v_res_3987_;
}
pub unsafe fn l_List_head_x3f(
    mut v_00_u03b1_3988_: *mut leanh::LeanObject,
    mut v_x_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = l_List_head_x3f___redArg(v_x_3989_);
    return v___x_3990_;
}
pub unsafe fn l_List_head_x3f___boxed(
    mut v_00_u03b1_3991_: *mut leanh::LeanObject,
    mut v_x_3992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3993_ = l_List_head_x3f(v_00_u03b1_3991_, v_x_3992_);
    leanh::lean_dec(v_x_3992_);
    return v_res_3993_;
}
pub unsafe fn l_List_headD___redArg(
    mut v_x_3994_: *mut leanh::LeanObject,
    mut v_x_3995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3994_) == 0 {
        leanh::lean_inc(v_x_3995_);
        return v_x_3995_;
    } else {
        let mut v_head_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_3996_ = leanh::lean_ctor_get(v_x_3994_, 0);
        leanh::lean_inc(v_head_3996_);
        return v_head_3996_;
    }
}
pub unsafe fn l_List_headD___redArg___boxed(
    mut v_x_3997_: *mut leanh::LeanObject,
    mut v_x_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_List_headD___redArg(v_x_3997_, v_x_3998_);
    leanh::lean_dec(v_x_3998_);
    leanh::lean_dec(v_x_3997_);
    return v_res_3999_;
}
pub unsafe fn l_List_headD(
    mut v_00_u03b1_4000_: *mut leanh::LeanObject,
    mut v_x_4001_: *mut leanh::LeanObject,
    mut v_x_4002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4001_) == 0 {
        leanh::lean_inc(v_x_4002_);
        return v_x_4002_;
    } else {
        let mut v_head_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_4003_ = leanh::lean_ctor_get(v_x_4001_, 0);
        leanh::lean_inc(v_head_4003_);
        return v_head_4003_;
    }
}
pub unsafe fn l_List_headD___boxed(
    mut v_00_u03b1_4004_: *mut leanh::LeanObject,
    mut v_x_4005_: *mut leanh::LeanObject,
    mut v_x_4006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4007_ = l_List_headD(v_00_u03b1_4004_, v_x_4005_, v_x_4006_);
    leanh::lean_dec(v_x_4006_);
    leanh::lean_dec(v_x_4005_);
    return v_res_4007_;
}
pub unsafe fn l_List_tail___redArg(
    mut v_x_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4008_) == 0 {
        return v_x_4008_;
    } else {
        let mut v_tail_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4009_ = leanh::lean_ctor_get(v_x_4008_, 1);
        leanh::lean_inc(v_tail_4009_);
        return v_tail_4009_;
    }
}
pub unsafe fn l_List_tail___redArg___boxed(
    mut v_x_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_List_tail___redArg(v_x_4010_);
    leanh::lean_dec(v_x_4010_);
    return v_res_4011_;
}
pub unsafe fn l_List_tail(
    mut v_00_u03b1_4012_: *mut leanh::LeanObject,
    mut v_x_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4013_) == 0 {
        return v_x_4013_;
    } else {
        let mut v_tail_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4014_ = leanh::lean_ctor_get(v_x_4013_, 1);
        leanh::lean_inc(v_tail_4014_);
        return v_tail_4014_;
    }
}
pub unsafe fn l_List_tail___boxed(
    mut v_00_u03b1_4015_: *mut leanh::LeanObject,
    mut v_x_4016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_List_tail(v_00_u03b1_4015_, v_x_4016_);
    leanh::lean_dec(v_x_4016_);
    return v_res_4017_;
}
pub unsafe fn l_List_tail_x3f___redArg(
    mut v_x_4018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4018_) == 0 {
        let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4019_ = leanh::lean_box(0);
        return v___x_4019_;
    } else {
        let mut v_tail_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4020_ = leanh::lean_ctor_get(v_x_4018_, 1);
        leanh::lean_inc(v_tail_4020_);
        v___x_4021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4021_, 0, v_tail_4020_);
        return v___x_4021_;
    }
}
pub unsafe fn l_List_tail_x3f___redArg___boxed(
    mut v_x_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_List_tail_x3f___redArg(v_x_4022_);
    leanh::lean_dec(v_x_4022_);
    return v_res_4023_;
}
pub unsafe fn l_List_tail_x3f(
    mut v_00_u03b1_4024_: *mut leanh::LeanObject,
    mut v_x_4025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_List_tail_x3f___redArg(v_x_4025_);
    return v___x_4026_;
}
pub unsafe fn l_List_tail_x3f___boxed(
    mut v_00_u03b1_4027_: *mut leanh::LeanObject,
    mut v_x_4028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_List_tail_x3f(v_00_u03b1_4027_, v_x_4028_);
    leanh::lean_dec(v_x_4028_);
    return v_res_4029_;
}
pub unsafe fn l_List_tailD___redArg(
    mut v_l_4030_: *mut leanh::LeanObject,
    mut v_fallback_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_4030_) == 0 {
        leanh::lean_inc(v_fallback_4031_);
        return v_fallback_4031_;
    } else {
        let mut v_tail_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4032_ = leanh::lean_ctor_get(v_l_4030_, 1);
        leanh::lean_inc(v_tail_4032_);
        return v_tail_4032_;
    }
}
pub unsafe fn l_List_tailD___redArg___boxed(
    mut v_l_4033_: *mut leanh::LeanObject,
    mut v_fallback_4034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_List_tailD___redArg(v_l_4033_, v_fallback_4034_);
    leanh::lean_dec(v_fallback_4034_);
    leanh::lean_dec(v_l_4033_);
    return v_res_4035_;
}
pub unsafe fn l_List_tailD(
    mut v_00_u03b1_4036_: *mut leanh::LeanObject,
    mut v_l_4037_: *mut leanh::LeanObject,
    mut v_fallback_4038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_4037_) == 0 {
        leanh::lean_inc(v_fallback_4038_);
        return v_fallback_4038_;
    } else {
        let mut v_tail_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4039_ = leanh::lean_ctor_get(v_l_4037_, 1);
        leanh::lean_inc(v_tail_4039_);
        return v_tail_4039_;
    }
}
pub unsafe fn l_List_tailD___boxed(
    mut v_00_u03b1_4040_: *mut leanh::LeanObject,
    mut v_l_4041_: *mut leanh::LeanObject,
    mut v_fallback_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ = l_List_tailD(v_00_u03b1_4040_, v_l_4041_, v_fallback_4042_);
    leanh::lean_dec(v_fallback_4042_);
    leanh::lean_dec(v_l_4041_);
    return v_res_4043_;
}
pub unsafe fn l_List_filter___redArg(
    mut v_p_4044_: *mut leanh::LeanObject,
    mut v_x_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4045_) == 0 {
                    leanh::lean_dec_ref(v_p_4044_);
                    return v_x_4045_;
                } else {
                    v_head_4046_ = leanh::lean_ctor_get(v_x_4045_, 0);
                    v_tail_4047_ = leanh::lean_ctor_get(v_x_4045_, 1);
                    v_isSharedCheck_4058_ = (!leanh::lean_is_exclusive(v_x_4045_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4049_ = v_x_4045_;
                        v_isShared_4050_ = v_isSharedCheck_4058_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4047_);
                        leanh::lean_inc(v_head_4046_);
                        leanh::lean_dec(v_x_4045_);
                        v___x_4049_ = leanh::lean_box(0);
                        v_isShared_4050_ = v_isSharedCheck_4058_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_p_4044_);
                leanh::lean_inc(v_head_4046_);
                v___x_4051_ = leanh::lean_apply_1(v_p_4044_, v_head_4046_);
                v___x_4052_ = (leanh::lean_unbox(v___x_4051_) as u8);
                if v___x_4052_ == 0 {
                    leanh::lean_del_object(v___x_4049_);
                    leanh::lean_dec(v_head_4046_);
                    v_x_4045_ = v_tail_4047_;
                    state = 0;
                    continue;
                } else {
                    v___x_4054_ = l_List_filter___redArg(v_p_4044_, v_tail_4047_);
                    if v_isShared_4050_ == 0 {
                        leanh::lean_ctor_set(v___x_4049_, 1, v___x_4054_);
                        v___x_4056_ = v___x_4049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4057_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_head_4046_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4054_);
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
    mut v_00_u03b1_4059_: *mut leanh::LeanObject,
    mut v_p_4060_: *mut leanh::LeanObject,
    mut v_x_4061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_List_filter___redArg(v_p_4060_, v_x_4061_);
    return v___x_4062_;
}
pub unsafe fn l_List_foldr___redArg(
    mut v_f_4063_: *mut leanh::LeanObject,
    mut v_init_4064_: *mut leanh::LeanObject,
    mut v_x_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4065_) == 0 {
        leanh::lean_dec(v_f_4063_);
        leanh::lean_inc(v_init_4064_);
        return v_init_4064_;
    } else {
        let mut v_head_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_4066_ = leanh::lean_ctor_get(v_x_4065_, 0);
        leanh::lean_inc(v_head_4066_);
        v_tail_4067_ = leanh::lean_ctor_get(v_x_4065_, 1);
        leanh::lean_inc(v_tail_4067_);
        leanh::lean_dec_ref_known(v_x_4065_, 2);
        leanh::lean_inc(v_f_4063_);
        v___x_4068_ = l_List_foldr___redArg(v_f_4063_, v_init_4064_, v_tail_4067_);
        v___x_4069_ = leanh::lean_apply_2(v_f_4063_, v_head_4066_, v___x_4068_);
        return v___x_4069_;
    }
}
pub unsafe fn l_List_foldr___redArg___boxed(
    mut v_f_4070_: *mut leanh::LeanObject,
    mut v_init_4071_: *mut leanh::LeanObject,
    mut v_x_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_List_foldr___redArg(v_f_4070_, v_init_4071_, v_x_4072_);
    leanh::lean_dec(v_init_4071_);
    return v_res_4073_;
}
pub unsafe fn l_List_foldr(
    mut v_00_u03b1_4074_: *mut leanh::LeanObject,
    mut v_00_u03b2_4075_: *mut leanh::LeanObject,
    mut v_f_4076_: *mut leanh::LeanObject,
    mut v_init_4077_: *mut leanh::LeanObject,
    mut v_x_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4079_ = l_List_foldr___redArg(v_f_4076_, v_init_4077_, v_x_4078_);
    return v___x_4079_;
}
pub unsafe fn l_List_foldr___boxed(
    mut v_00_u03b1_4080_: *mut leanh::LeanObject,
    mut v_00_u03b2_4081_: *mut leanh::LeanObject,
    mut v_f_4082_: *mut leanh::LeanObject,
    mut v_init_4083_: *mut leanh::LeanObject,
    mut v_x_4084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_List_foldr(
        v_00_u03b1_4080_,
        v_00_u03b2_4081_,
        v_f_4082_,
        v_init_4083_,
        v_x_4084_,
    );
    leanh::lean_dec(v_init_4083_);
    return v_res_4085_;
}
pub unsafe fn l_List_reverseAux___redArg(
    mut v_x_4086_: *mut leanh::LeanObject,
    mut v_x_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4086_) == 0 {
                    return v_x_4087_;
                } else {
                    v_head_4088_ = leanh::lean_ctor_get(v_x_4086_, 0);
                    v_tail_4089_ = leanh::lean_ctor_get(v_x_4086_, 1);
                    v_isSharedCheck_4097_ = (!leanh::lean_is_exclusive(v_x_4086_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4091_ = v_x_4086_;
                        v_isShared_4092_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4089_);
                        leanh::lean_inc(v_head_4088_);
                        leanh::lean_dec(v_x_4086_);
                        v___x_4091_ = leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4092_ == 0 {
                    leanh::lean_ctor_set(v___x_4091_, 1, v_x_4087_);
                    v___x_4094_ = v___x_4091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_head_4088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 1, v_x_4087_);
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
    mut v_00_u03b1_4098_: *mut leanh::LeanObject,
    mut v_x_4099_: *mut leanh::LeanObject,
    mut v_x_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = l_List_reverseAux___redArg(v_x_4099_, v_x_4100_);
    return v___x_4101_;
}
pub unsafe fn l_List_reverse___redArg(
    mut v_as_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4103_ = leanh::lean_box(0);
    v___x_4104_ = l_List_reverseAux___redArg(v_as_4102_, v___x_4103_);
    return v___x_4104_;
}
pub unsafe fn l_List_reverse(
    mut v_00_u03b1_4105_: *mut leanh::LeanObject,
    mut v_as_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_List_reverse___redArg(v_as_4106_);
    return v___x_4107_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter___redArg(
    mut v_x_4108_: *mut leanh::LeanObject,
    mut v_x_4109_: *mut leanh::LeanObject,
    mut v_h__1_4110_: *mut leanh::LeanObject,
    mut v_h__2_4111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4108_) == 0 {
        let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4111_);
        v___x_4112_ = leanh::lean_apply_1(v_h__1_4110_, v_x_4109_);
        return v___x_4112_;
    } else {
        let mut v_head_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4110_);
        v_head_4113_ = leanh::lean_ctor_get(v_x_4108_, 0);
        leanh::lean_inc(v_head_4113_);
        v_tail_4114_ = leanh::lean_ctor_get(v_x_4108_, 1);
        leanh::lean_inc(v_tail_4114_);
        leanh::lean_dec_ref_known(v_x_4108_, 2);
        v___x_4115_ =
            leanh::lean_apply_3(v_h__2_4111_, v_head_4113_, v_tail_4114_, v_x_4109_);
        return v___x_4115_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_reverseAux_match__1_splitter(
    mut v_00_u03b1_4116_: *mut leanh::LeanObject,
    mut v_motive_4117_: *mut leanh::LeanObject,
    mut v_x_4118_: *mut leanh::LeanObject,
    mut v_x_4119_: *mut leanh::LeanObject,
    mut v_h__1_4120_: *mut leanh::LeanObject,
    mut v_h__2_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4118_) == 0 {
        let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4121_);
        v___x_4122_ = leanh::lean_apply_1(v_h__1_4120_, v_x_4119_);
        return v___x_4122_;
    } else {
        let mut v_head_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4120_);
        v_head_4123_ = leanh::lean_ctor_get(v_x_4118_, 0);
        leanh::lean_inc(v_head_4123_);
        v_tail_4124_ = leanh::lean_ctor_get(v_x_4118_, 1);
        leanh::lean_inc(v_tail_4124_);
        leanh::lean_dec_ref_known(v_x_4118_, 2);
        v___x_4125_ =
            leanh::lean_apply_3(v_h__2_4121_, v_head_4123_, v_tail_4124_, v_x_4119_);
        return v___x_4125_;
    }
}
pub unsafe fn l_List_appendTR___redArg(
    mut v_as_4126_: *mut leanh::LeanObject,
    mut v_bs_4127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l_List_reverse___redArg(v_as_4126_);
    v___x_4129_ = l_List_reverseAux___redArg(v___x_4128_, v_bs_4127_);
    return v___x_4129_;
}
pub unsafe fn l_List_appendTR(
    mut v_00_u03b1_4130_: *mut leanh::LeanObject,
    mut v_as_4131_: *mut leanh::LeanObject,
    mut v_bs_4132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = l_List_appendTR___redArg(v_as_4131_, v_bs_4132_);
    return v___x_4133_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_append_match__1_splitter___redArg(
    mut v_x_4134_: *mut leanh::LeanObject,
    mut v_x_4135_: *mut leanh::LeanObject,
    mut v_h__1_4136_: *mut leanh::LeanObject,
    mut v_h__2_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4134_) == 0 {
        let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4137_);
        v___x_4138_ = leanh::lean_apply_1(v_h__1_4136_, v_x_4135_);
        return v___x_4138_;
    } else {
        let mut v_head_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4136_);
        v_head_4139_ = leanh::lean_ctor_get(v_x_4134_, 0);
        leanh::lean_inc(v_head_4139_);
        v_tail_4140_ = leanh::lean_ctor_get(v_x_4134_, 1);
        leanh::lean_inc(v_tail_4140_);
        leanh::lean_dec_ref_known(v_x_4134_, 2);
        v___x_4141_ =
            leanh::lean_apply_3(v_h__2_4137_, v_head_4139_, v_tail_4140_, v_x_4135_);
        return v___x_4141_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_append_match__1_splitter(
    mut v_00_u03b1_4142_: *mut leanh::LeanObject,
    mut v_motive_4143_: *mut leanh::LeanObject,
    mut v_x_4144_: *mut leanh::LeanObject,
    mut v_x_4145_: *mut leanh::LeanObject,
    mut v_h__1_4146_: *mut leanh::LeanObject,
    mut v_h__2_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4144_) == 0 {
        let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4147_);
        v___x_4148_ = leanh::lean_apply_1(v_h__1_4146_, v_x_4145_);
        return v___x_4148_;
    } else {
        let mut v_head_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4146_);
        v_head_4149_ = leanh::lean_ctor_get(v_x_4144_, 0);
        leanh::lean_inc(v_head_4149_);
        v_tail_4150_ = leanh::lean_ctor_get(v_x_4144_, 1);
        leanh::lean_inc(v_tail_4150_);
        leanh::lean_dec_ref_known(v_x_4144_, 2);
        v___x_4151_ =
            leanh::lean_apply_3(v_h__2_4147_, v_head_4149_, v_tail_4150_, v_x_4145_);
        return v___x_4151_;
    }
}
pub unsafe fn l_List_instAppend(
    mut v_00_u03b1_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_List_instAppend___closed__0;
    return v___x_4154_;
}
pub unsafe fn l_List_singleton___redArg(
    mut v_a_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = leanh::lean_box(0);
    v___x_4157_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4157_, 0, v_a_4155_);
    leanh::lean_ctor_set(v___x_4157_, 1, v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_List_singleton(
    mut v_00_u03b1_4158_: *mut leanh::LeanObject,
    mut v_a_4159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = leanh::lean_box(0);
    v___x_4161_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4161_, 0, v_a_4159_);
    leanh::lean_ctor_set(v___x_4161_, 1, v___x_4160_);
    return v___x_4161_;
}
pub unsafe fn l_List_replicate___redArg(
    mut v_x_4162_: *mut leanh::LeanObject,
    mut v_x_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4165_: u8 = 0;
    v_zero_4164_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_4165_ = lean_nat_dec_eq(v_x_4162_, v_zero_4164_);
    if v_isZero_4165_ == 1 {
        let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4163_);
        v___x_4166_ = leanh::lean_box(0);
        return v___x_4166_;
    } else {
        let mut v_one_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_4167_ = leanh::lean_unsigned_to_nat(1);
        v_n_4168_ = lean_nat_sub(v_x_4162_, v_one_4167_);
        leanh::lean_inc(v_x_4163_);
        v___x_4169_ = l_List_replicate___redArg(v_n_4168_, v_x_4163_);
        leanh::lean_dec(v_n_4168_);
        v___x_4170_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4170_, 0, v_x_4163_);
        leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
        return v___x_4170_;
    }
}
pub unsafe fn l_List_replicate___redArg___boxed(
    mut v_x_4171_: *mut leanh::LeanObject,
    mut v_x_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4173_ = l_List_replicate___redArg(v_x_4171_, v_x_4172_);
    leanh::lean_dec(v_x_4171_);
    return v_res_4173_;
}
pub unsafe fn l_List_replicate(
    mut v_00_u03b1_4174_: *mut leanh::LeanObject,
    mut v_x_4175_: *mut leanh::LeanObject,
    mut v_x_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l_List_replicate___redArg(v_x_4175_, v_x_4176_);
    return v___x_4177_;
}
pub unsafe fn l_List_replicate___boxed(
    mut v_00_u03b1_4178_: *mut leanh::LeanObject,
    mut v_x_4179_: *mut leanh::LeanObject,
    mut v_x_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_List_replicate(v_00_u03b1_4178_, v_x_4179_, v_x_4180_);
    leanh::lean_dec(v_x_4179_);
    return v_res_4181_;
}
pub unsafe fn l_List_leftpad___redArg(
    mut v_n_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_l_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4185_ = l_List_length___redArg(v_l_4184_);
    v___x_4186_ = lean_nat_sub(v_n_4182_, v___x_4185_);
    leanh::lean_dec(v___x_4185_);
    v___x_4187_ = l_List_replicate___redArg(v___x_4186_, v_a_4183_);
    leanh::lean_dec(v___x_4186_);
    v___x_4188_ = l_List_appendTR___redArg(v___x_4187_, v_l_4184_);
    return v___x_4188_;
}
pub unsafe fn l_List_leftpad___redArg___boxed(
    mut v_n_4189_: *mut leanh::LeanObject,
    mut v_a_4190_: *mut leanh::LeanObject,
    mut v_l_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ = l_List_leftpad___redArg(v_n_4189_, v_a_4190_, v_l_4191_);
    leanh::lean_dec(v_n_4189_);
    return v_res_4192_;
}
pub unsafe fn l_List_leftpad(
    mut v_00_u03b1_4193_: *mut leanh::LeanObject,
    mut v_n_4194_: *mut leanh::LeanObject,
    mut v_a_4195_: *mut leanh::LeanObject,
    mut v_l_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_List_leftpad___redArg(v_n_4194_, v_a_4195_, v_l_4196_);
    return v___x_4197_;
}
pub unsafe fn l_List_leftpad___boxed(
    mut v_00_u03b1_4198_: *mut leanh::LeanObject,
    mut v_n_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_l_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_List_leftpad(v_00_u03b1_4198_, v_n_4199_, v_a_4200_, v_l_4201_);
    leanh::lean_dec(v_n_4199_);
    return v_res_4202_;
}
pub unsafe fn l_List_rightpad___redArg(
    mut v_n_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
    mut v_l_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = l_List_length___redArg(v_l_4205_);
    v___x_4207_ = lean_nat_sub(v_n_4203_, v___x_4206_);
    leanh::lean_dec(v___x_4206_);
    v___x_4208_ = l_List_replicate___redArg(v___x_4207_, v_a_4204_);
    leanh::lean_dec(v___x_4207_);
    v___x_4209_ = l_List_appendTR___redArg(v_l_4205_, v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn l_List_rightpad___redArg___boxed(
    mut v_n_4210_: *mut leanh::LeanObject,
    mut v_a_4211_: *mut leanh::LeanObject,
    mut v_l_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_List_rightpad___redArg(v_n_4210_, v_a_4211_, v_l_4212_);
    leanh::lean_dec(v_n_4210_);
    return v_res_4213_;
}
pub unsafe fn l_List_rightpad(
    mut v_00_u03b1_4214_: *mut leanh::LeanObject,
    mut v_n_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
    mut v_l_4217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_List_rightpad___redArg(v_n_4215_, v_a_4216_, v_l_4217_);
    return v___x_4218_;
}
pub unsafe fn l_List_rightpad___boxed(
    mut v_00_u03b1_4219_: *mut leanh::LeanObject,
    mut v_n_4220_: *mut leanh::LeanObject,
    mut v_a_4221_: *mut leanh::LeanObject,
    mut v_l_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4223_ = l_List_rightpad(v_00_u03b1_4219_, v_n_4220_, v_a_4221_, v_l_4222_);
    leanh::lean_dec(v_n_4220_);
    return v_res_4223_;
}
pub unsafe fn l_List_instEmptyCollection(
    mut v_00_u03b1_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = leanh::lean_box(0);
    return v___x_4225_;
}
pub unsafe fn l_List_isEmpty___redArg(mut v_x_4226_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_4226_) == 0 {
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
    mut v_x_4229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4230_: u8 = 0;
    let mut v_r_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4230_ = l_List_isEmpty___redArg(v_x_4229_);
    leanh::lean_dec(v_x_4229_);
    v_r_4231_ = leanh::lean_box((v_res_4230_) as usize);
    return v_r_4231_;
}
pub unsafe fn l_List_isEmpty(
    mut v_00_u03b1_4232_: *mut leanh::LeanObject,
    mut v_x_4233_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4234_: u8 = 0;
    v___x_4234_ = l_List_isEmpty___redArg(v_x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_List_isEmpty___boxed(
    mut v_00_u03b1_4235_: *mut leanh::LeanObject,
    mut v_x_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4237_: u8 = 0;
    let mut v_r_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_List_isEmpty(v_00_u03b1_4235_, v_x_4236_);
    leanh::lean_dec(v_x_4236_);
    v_r_4238_ = leanh::lean_box((v_res_4237_) as usize);
    return v_r_4238_;
}
pub unsafe fn l_List_elem___redArg(
    mut v_inst_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_x_4241_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4242_: u8 = 0;
    let mut v_head_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4241_) == 0 {
                    leanh::lean_dec(v_a_4240_);
                    leanh::lean_dec_ref(v_inst_4239_);
                    v___x_4242_ = 0;
                    return v___x_4242_;
                } else {
                    v_head_4243_ = leanh::lean_ctor_get(v_x_4241_, 0);
                    leanh::lean_inc(v_head_4243_);
                    v_tail_4244_ = leanh::lean_ctor_get(v_x_4241_, 1);
                    leanh::lean_inc(v_tail_4244_);
                    leanh::lean_dec_ref_known(v_x_4241_, 2);
                    leanh::lean_inc_ref(v_inst_4239_);
                    leanh::lean_inc(v_a_4240_);
                    v___x_4245_ = leanh::lean_apply_2(v_inst_4239_, v_a_4240_, v_head_4243_);
                    v___x_4246_ = (leanh::lean_unbox(v___x_4245_) as u8);
                    if v___x_4246_ == 0 {
                        v_x_4241_ = v_tail_4244_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_4244_);
                        leanh::lean_dec(v_a_4240_);
                        leanh::lean_dec_ref(v_inst_4239_);
                        v___x_4248_ = (leanh::lean_unbox(v___x_4245_) as u8);
                        return v___x_4248_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___redArg___boxed(
    mut v_inst_4249_: *mut leanh::LeanObject,
    mut v_a_4250_: *mut leanh::LeanObject,
    mut v_x_4251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4252_: u8 = 0;
    let mut v_r_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4252_ = l_List_elem___redArg(v_inst_4249_, v_a_4250_, v_x_4251_);
    v_r_4253_ = leanh::lean_box((v_res_4252_) as usize);
    return v_r_4253_;
}
pub unsafe fn l_List_elem(
    mut v_00_u03b1_4254_: *mut leanh::LeanObject,
    mut v_inst_4255_: *mut leanh::LeanObject,
    mut v_a_4256_: *mut leanh::LeanObject,
    mut v_x_4257_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4258_: u8 = 0;
    v___x_4258_ = l_List_elem___redArg(v_inst_4255_, v_a_4256_, v_x_4257_);
    return v___x_4258_;
}
pub unsafe fn l_List_elem___boxed(
    mut v_00_u03b1_4259_: *mut leanh::LeanObject,
    mut v_inst_4260_: *mut leanh::LeanObject,
    mut v_a_4261_: *mut leanh::LeanObject,
    mut v_x_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4263_: u8 = 0;
    let mut v_r_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4263_ = l_List_elem(v_00_u03b1_4259_, v_inst_4260_, v_a_4261_, v_x_4262_);
    v_r_4264_ = leanh::lean_box((v_res_4263_) as usize);
    return v_r_4264_;
}
pub unsafe fn l_List_contains___redArg(
    mut v_inst_4265_: *mut leanh::LeanObject,
    mut v_as_4266_: *mut leanh::LeanObject,
    mut v_a_4267_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4268_: u8 = 0;
    v___x_4268_ = l_List_elem___redArg(v_inst_4265_, v_a_4267_, v_as_4266_);
    return v___x_4268_;
}
pub unsafe fn l_List_contains___redArg___boxed(
    mut v_inst_4269_: *mut leanh::LeanObject,
    mut v_as_4270_: *mut leanh::LeanObject,
    mut v_a_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4272_: u8 = 0;
    let mut v_r_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_List_contains___redArg(v_inst_4269_, v_as_4270_, v_a_4271_);
    v_r_4273_ = leanh::lean_box((v_res_4272_) as usize);
    return v_r_4273_;
}
pub unsafe fn l_List_contains(
    mut v_00_u03b1_4274_: *mut leanh::LeanObject,
    mut v_inst_4275_: *mut leanh::LeanObject,
    mut v_as_4276_: *mut leanh::LeanObject,
    mut v_a_4277_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4278_: u8 = 0;
    v___x_4278_ = l_List_elem___redArg(v_inst_4275_, v_a_4277_, v_as_4276_);
    return v___x_4278_;
}
pub unsafe fn l_List_contains___boxed(
    mut v_00_u03b1_4279_: *mut leanh::LeanObject,
    mut v_inst_4280_: *mut leanh::LeanObject,
    mut v_as_4281_: *mut leanh::LeanObject,
    mut v_a_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4283_: u8 = 0;
    let mut v_r_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4283_ = l_List_contains(v_00_u03b1_4279_, v_inst_4280_, v_as_4281_, v_a_4282_);
    v_r_4284_ = leanh::lean_box((v_res_4283_) as usize);
    return v_r_4284_;
}
pub unsafe fn l_List_instMembership(
    mut v_00_u03b1_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = leanh::lean_box(0);
    return v___x_4286_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_4287_: *mut leanh::LeanObject,
    mut v_h__1_4288_: *mut leanh::LeanObject,
    mut v_h__2_4289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4287_) == 0 {
        let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4289_);
        v___x_4290_ = leanh::lean_box(0);
        v___x_4291_ = leanh::lean_apply_1(v_h__1_4288_, v___x_4290_);
        return v___x_4291_;
    } else {
        let mut v_head_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4288_);
        v_head_4292_ = leanh::lean_ctor_get(v_x_4287_, 0);
        leanh::lean_inc(v_head_4292_);
        v_tail_4293_ = leanh::lean_ctor_get(v_x_4287_, 1);
        leanh::lean_inc(v_tail_4293_);
        leanh::lean_dec_ref_known(v_x_4287_, 2);
        v___x_4294_ = leanh::lean_apply_2(v_h__2_4289_, v_head_4292_, v_tail_4293_);
        return v___x_4294_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_4295_: *mut leanh::LeanObject,
    mut v_motive_4296_: *mut leanh::LeanObject,
    mut v_x_4297_: *mut leanh::LeanObject,
    mut v_h__1_4298_: *mut leanh::LeanObject,
    mut v_h__2_4299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4297_) == 0 {
        let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4299_);
        v___x_4300_ = leanh::lean_box(0);
        v___x_4301_ = leanh::lean_apply_1(v_h__1_4298_, v___x_4300_);
        return v___x_4301_;
    } else {
        let mut v_head_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4298_);
        v_head_4302_ = leanh::lean_ctor_get(v_x_4297_, 0);
        leanh::lean_inc(v_head_4302_);
        v_tail_4303_ = leanh::lean_ctor_get(v_x_4297_, 1);
        leanh::lean_inc(v_tail_4303_);
        leanh::lean_dec_ref_known(v_x_4297_, 2);
        v___x_4304_ = leanh::lean_apply_2(v_h__2_4299_, v_head_4302_, v_tail_4303_);
        return v___x_4304_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(
    mut v_x_4305_: u8,
    mut v_h__1_4306_: *mut leanh::LeanObject,
    mut v_h__2_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_4305_ == 0 {
        let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4306_);
        v___x_4308_ = leanh::lean_box(0);
        v___x_4309_ = leanh::lean_apply_1(v_h__2_4307_, v___x_4308_);
        return v___x_4309_;
    } else {
        let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4307_);
        v___x_4310_ = leanh::lean_box(0);
        v___x_4311_ = leanh::lean_apply_1(v_h__1_4306_, v___x_4310_);
        return v___x_4311_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_4312_: *mut leanh::LeanObject,
    mut v_h__1_4313_: *mut leanh::LeanObject,
    mut v_h__2_4314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_4315_: u8 = 0;
    let mut v_res_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_4315_ = (leanh::lean_unbox(v_x_4312_) as u8);
    v_res_4316_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_4315_,
        v_h__1_4313_,
        v_h__2_4314_,
    );
    return v_res_4316_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(
    mut v_motive_4317_: *mut leanh::LeanObject,
    mut v_x_4318_: u8,
    mut v_h__1_4319_: *mut leanh::LeanObject,
    mut v_h__2_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_4318_ == 0 {
        let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4319_);
        v___x_4321_ = leanh::lean_box(0);
        v___x_4322_ = leanh::lean_apply_1(v_h__2_4320_, v___x_4321_);
        return v___x_4322_;
    } else {
        let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4320_);
        v___x_4323_ = leanh::lean_box(0);
        v___x_4324_ = leanh::lean_apply_1(v_h__1_4319_, v___x_4323_);
        return v___x_4324_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter___boxed(
    mut v_motive_4325_: *mut leanh::LeanObject,
    mut v_x_4326_: *mut leanh::LeanObject,
    mut v_h__1_4327_: *mut leanh::LeanObject,
    mut v_h__2_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_4329_: u8 = 0;
    let mut v_res_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_4329_ = (leanh::lean_unbox(v_x_4326_) as u8);
    v_res_4330_ = l___private_Init_Data_List_Basic_0__List_filter_match__1_splitter(
        v_motive_4325_,
        v_x_37__boxed_4329_,
        v_h__1_4327_,
        v_h__2_4328_,
    );
    return v_res_4330_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___redArg(
    mut v_inst_4331_: *mut leanh::LeanObject,
    mut v_a_4332_: *mut leanh::LeanObject,
    mut v_as_4333_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4334_: u8 = 0;
    v___x_4334_ = l_List_elem___redArg(v_inst_4331_, v_a_4332_, v_as_4333_);
    return v___x_4334_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___redArg___boxed(
    mut v_inst_4335_: *mut leanh::LeanObject,
    mut v_a_4336_: *mut leanh::LeanObject,
    mut v_as_4337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4338_: u8 = 0;
    let mut v_r_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_List_instDecidableMemOfLawfulBEq___redArg(v_inst_4335_, v_a_4336_, v_as_4337_);
    v_r_4339_ = leanh::lean_box((v_res_4338_) as usize);
    return v_r_4339_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq(
    mut v_00_u03b1_4340_: *mut leanh::LeanObject,
    mut v_inst_4341_: *mut leanh::LeanObject,
    mut v_inst_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
    mut v_as_4344_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4345_: u8 = 0;
    v___x_4345_ = l_List_elem___redArg(v_inst_4341_, v_a_4343_, v_as_4344_);
    return v___x_4345_;
}
pub unsafe fn l_List_instDecidableMemOfLawfulBEq___boxed(
    mut v_00_u03b1_4346_: *mut leanh::LeanObject,
    mut v_inst_4347_: *mut leanh::LeanObject,
    mut v_inst_4348_: *mut leanh::LeanObject,
    mut v_a_4349_: *mut leanh::LeanObject,
    mut v_as_4350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4351_: u8 = 0;
    let mut v_r_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4351_ = l_List_instDecidableMemOfLawfulBEq(
        v_00_u03b1_4346_,
        v_inst_4347_,
        v_inst_4348_,
        v_a_4349_,
        v_as_4350_,
    );
    v_r_4352_ = leanh::lean_box((v_res_4351_) as usize);
    return v_r_4352_;
}
pub unsafe fn l_List_decidableBEx___redArg(
    mut v_inst_4353_: *mut leanh::LeanObject,
    mut v_x_4354_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4355_: u8 = 0;
    let mut v_head_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4354_) == 0 {
                    leanh::lean_dec_ref(v_inst_4353_);
                    v___x_4355_ = 0;
                    return v___x_4355_;
                } else {
                    v_head_4356_ = leanh::lean_ctor_get(v_x_4354_, 0);
                    leanh::lean_inc(v_head_4356_);
                    v_tail_4357_ = leanh::lean_ctor_get(v_x_4354_, 1);
                    leanh::lean_inc(v_tail_4357_);
                    leanh::lean_dec_ref_known(v_x_4354_, 2);
                    leanh::lean_inc_ref(v_inst_4353_);
                    v___x_4358_ = leanh::lean_apply_1(v_inst_4353_, v_head_4356_);
                    v___x_4359_ = (leanh::lean_unbox(v___x_4358_) as u8);
                    if v___x_4359_ == 0 {
                        v_x_4354_ = v_tail_4357_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_4357_);
                        leanh::lean_dec_ref(v_inst_4353_);
                        v___x_4361_ = (leanh::lean_unbox(v___x_4358_) as u8);
                        return v___x_4361_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_decidableBEx___redArg___boxed(
    mut v_inst_4362_: *mut leanh::LeanObject,
    mut v_x_4363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4364_: u8 = 0;
    let mut v_r_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4364_ = l_List_decidableBEx___redArg(v_inst_4362_, v_x_4363_);
    v_r_4365_ = leanh::lean_box((v_res_4364_) as usize);
    return v_r_4365_;
}
pub unsafe fn l_List_decidableBEx(
    mut v_00_u03b1_4366_: *mut leanh::LeanObject,
    mut v_p_4367_: *mut leanh::LeanObject,
    mut v_inst_4368_: *mut leanh::LeanObject,
    mut v_x_4369_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4370_: u8 = 0;
    v___x_4370_ = l_List_decidableBEx___redArg(v_inst_4368_, v_x_4369_);
    return v___x_4370_;
}
pub unsafe fn l_List_decidableBEx___boxed(
    mut v_00_u03b1_4371_: *mut leanh::LeanObject,
    mut v_p_4372_: *mut leanh::LeanObject,
    mut v_inst_4373_: *mut leanh::LeanObject,
    mut v_x_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: u8 = 0;
    let mut v_r_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_List_decidableBEx(v_00_u03b1_4371_, v_p_4372_, v_inst_4373_, v_x_4374_);
    v_r_4376_ = leanh::lean_box((v_res_4375_) as usize);
    return v_r_4376_;
}
pub unsafe fn l_List_decidableBAll___redArg(
    mut v_inst_4377_: *mut leanh::LeanObject,
    mut v_x_4378_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4379_: u8 = 0;
    let mut v_head_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4378_) == 0 {
                    leanh::lean_dec_ref(v_inst_4377_);
                    v___x_4379_ = 1;
                    return v___x_4379_;
                } else {
                    v_head_4380_ = leanh::lean_ctor_get(v_x_4378_, 0);
                    leanh::lean_inc(v_head_4380_);
                    v_tail_4381_ = leanh::lean_ctor_get(v_x_4378_, 1);
                    leanh::lean_inc(v_tail_4381_);
                    leanh::lean_dec_ref_known(v_x_4378_, 2);
                    leanh::lean_inc_ref(v_inst_4377_);
                    v___x_4382_ = leanh::lean_apply_1(v_inst_4377_, v_head_4380_);
                    v___x_4383_ = (leanh::lean_unbox(v___x_4382_) as u8);
                    if v___x_4383_ == 0 {
                        leanh::lean_dec(v_tail_4381_);
                        leanh::lean_dec_ref(v_inst_4377_);
                        v___x_4384_ = (leanh::lean_unbox(v___x_4382_) as u8);
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
    mut v_inst_4386_: *mut leanh::LeanObject,
    mut v_x_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4388_: u8 = 0;
    let mut v_r_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4388_ = l_List_decidableBAll___redArg(v_inst_4386_, v_x_4387_);
    v_r_4389_ = leanh::lean_box((v_res_4388_) as usize);
    return v_r_4389_;
}
pub unsafe fn l_List_decidableBAll(
    mut v_00_u03b1_4390_: *mut leanh::LeanObject,
    mut v_p_4391_: *mut leanh::LeanObject,
    mut v_inst_4392_: *mut leanh::LeanObject,
    mut v_x_4393_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4394_: u8 = 0;
    v___x_4394_ = l_List_decidableBAll___redArg(v_inst_4392_, v_x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_List_decidableBAll___boxed(
    mut v_00_u03b1_4395_: *mut leanh::LeanObject,
    mut v_p_4396_: *mut leanh::LeanObject,
    mut v_inst_4397_: *mut leanh::LeanObject,
    mut v_x_4398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4399_: u8 = 0;
    let mut v_r_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ = l_List_decidableBAll(v_00_u03b1_4395_, v_p_4396_, v_inst_4397_, v_x_4398_);
    v_r_4400_ = leanh::lean_box((v_res_4399_) as usize);
    return v_r_4400_;
}
pub unsafe fn l_List_take___redArg(
    mut v_x_4401_: *mut leanh::LeanObject,
    mut v_x_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4404_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v_one_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4403_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4404_ = lean_nat_dec_eq(v_x_4401_, v_zero_4403_);
                if v_isZero_4404_ == 1 {
                    leanh::lean_dec(v_x_4402_);
                    v___x_4405_ = leanh::lean_box(0);
                    return v___x_4405_;
                } else {
                    if leanh::lean_obj_tag(v_x_4402_) == 0 {
                        return v_x_4402_;
                    } else {
                        v_head_4406_ = leanh::lean_ctor_get(v_x_4402_, 0);
                        v_tail_4407_ = leanh::lean_ctor_get(v_x_4402_, 1);
                        v_isSharedCheck_4417_ = (!leanh::lean_is_exclusive(v_x_4402_)) as u8;
                        if v_isSharedCheck_4417_ == 0 {
                            v___x_4409_ = v_x_4402_;
                            v_isShared_4410_ = v_isSharedCheck_4417_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_4407_);
                            leanh::lean_inc(v_head_4406_);
                            leanh::lean_dec(v_x_4402_);
                            v___x_4409_ = leanh::lean_box(0);
                            v_isShared_4410_ = v_isSharedCheck_4417_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_4411_ = leanh::lean_unsigned_to_nat(1);
                v_n_4412_ = lean_nat_sub(v_x_4401_, v_one_4411_);
                v___x_4413_ = l_List_take___redArg(v_n_4412_, v_tail_4407_);
                leanh::lean_dec(v_n_4412_);
                if v_isShared_4410_ == 0 {
                    leanh::lean_ctor_set(v___x_4409_, 1, v___x_4413_);
                    v___x_4415_ = v___x_4409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_head_4406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4413_);
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
    mut v_x_4418_: *mut leanh::LeanObject,
    mut v_x_4419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4420_ = l_List_take___redArg(v_x_4418_, v_x_4419_);
    leanh::lean_dec(v_x_4418_);
    return v_res_4420_;
}
pub unsafe fn l_List_take(
    mut v_00_u03b1_4421_: *mut leanh::LeanObject,
    mut v_x_4422_: *mut leanh::LeanObject,
    mut v_x_4423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4424_ = l_List_take___redArg(v_x_4422_, v_x_4423_);
    return v___x_4424_;
}
pub unsafe fn l_List_take___boxed(
    mut v_00_u03b1_4425_: *mut leanh::LeanObject,
    mut v_x_4426_: *mut leanh::LeanObject,
    mut v_x_4427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_List_take(v_00_u03b1_4425_, v_x_4426_, v_x_4427_);
    leanh::lean_dec(v_x_4426_);
    return v_res_4428_;
}
pub unsafe fn l_List_drop___redArg(
    mut v_x_4429_: *mut leanh::LeanObject,
    mut v_x_4430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4432_: u8 = 0;
    let mut v_tail_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4431_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4432_ = lean_nat_dec_eq(v_x_4429_, v_zero_4431_);
                if v_isZero_4432_ == 1 {
                    leanh::lean_dec(v_x_4429_);
                    leanh::lean_inc(v_x_4430_);
                    return v_x_4430_;
                } else {
                    if leanh::lean_obj_tag(v_x_4430_) == 0 {
                        leanh::lean_dec(v_x_4429_);
                        return v_x_4430_;
                    } else {
                        v_tail_4433_ = leanh::lean_ctor_get(v_x_4430_, 1);
                        v_one_4434_ = leanh::lean_unsigned_to_nat(1);
                        v_n_4435_ = lean_nat_sub(v_x_4429_, v_one_4434_);
                        leanh::lean_dec(v_x_4429_);
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
    mut v_x_4437_: *mut leanh::LeanObject,
    mut v_x_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_List_drop___redArg(v_x_4437_, v_x_4438_);
    leanh::lean_dec(v_x_4438_);
    return v_res_4439_;
}
pub unsafe fn l_List_drop(
    mut v_00_u03b1_4440_: *mut leanh::LeanObject,
    mut v_x_4441_: *mut leanh::LeanObject,
    mut v_x_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_List_drop___redArg(v_x_4441_, v_x_4442_);
    return v___x_4443_;
}
pub unsafe fn l_List_drop___boxed(
    mut v_00_u03b1_4444_: *mut leanh::LeanObject,
    mut v_x_4445_: *mut leanh::LeanObject,
    mut v_x_4446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4447_ = l_List_drop(v_00_u03b1_4444_, v_x_4445_, v_x_4446_);
    leanh::lean_dec(v_x_4446_);
    return v_res_4447_;
}
pub unsafe fn l_List_extract___redArg(
    mut v_l_4448_: *mut leanh::LeanObject,
    mut v_start_4449_: *mut leanh::LeanObject,
    mut v_stop_4450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4451_ = lean_nat_sub(v_stop_4450_, v_start_4449_);
    v___x_4452_ = l_List_drop___redArg(v_start_4449_, v_l_4448_);
    v___x_4453_ = l_List_take___redArg(v___x_4451_, v___x_4452_);
    leanh::lean_dec(v___x_4451_);
    return v___x_4453_;
}
pub unsafe fn l_List_extract___redArg___boxed(
    mut v_l_4454_: *mut leanh::LeanObject,
    mut v_start_4455_: *mut leanh::LeanObject,
    mut v_stop_4456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_List_extract___redArg(v_l_4454_, v_start_4455_, v_stop_4456_);
    leanh::lean_dec(v_stop_4456_);
    leanh::lean_dec(v_l_4454_);
    return v_res_4457_;
}
pub unsafe fn l_List_extract(
    mut v_00_u03b1_4458_: *mut leanh::LeanObject,
    mut v_l_4459_: *mut leanh::LeanObject,
    mut v_start_4460_: *mut leanh::LeanObject,
    mut v_stop_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4462_ = lean_nat_sub(v_stop_4461_, v_start_4460_);
    v___x_4463_ = l_List_drop___redArg(v_start_4460_, v_l_4459_);
    v___x_4464_ = l_List_take___redArg(v___x_4462_, v___x_4463_);
    leanh::lean_dec(v___x_4462_);
    return v___x_4464_;
}
pub unsafe fn l_List_extract___boxed(
    mut v_00_u03b1_4465_: *mut leanh::LeanObject,
    mut v_l_4466_: *mut leanh::LeanObject,
    mut v_start_4467_: *mut leanh::LeanObject,
    mut v_stop_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = l_List_extract(v_00_u03b1_4465_, v_l_4466_, v_start_4467_, v_stop_4468_);
    leanh::lean_dec(v_stop_4468_);
    leanh::lean_dec(v_l_4466_);
    return v_res_4469_;
}
pub unsafe fn l_List_takeWhile___redArg(
    mut v_p_4470_: *mut leanh::LeanObject,
    mut v_x_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4471_) == 0 {
                    leanh::lean_dec_ref(v_p_4470_);
                    return v_x_4471_;
                } else {
                    v_head_4472_ = leanh::lean_ctor_get(v_x_4471_, 0);
                    v_tail_4473_ = leanh::lean_ctor_get(v_x_4471_, 1);
                    v_isSharedCheck_4484_ = (!leanh::lean_is_exclusive(v_x_4471_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4475_ = v_x_4471_;
                        v_isShared_4476_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4473_);
                        leanh::lean_inc(v_head_4472_);
                        leanh::lean_dec(v_x_4471_);
                        v___x_4475_ = leanh::lean_box(0);
                        v_isShared_4476_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_p_4470_);
                leanh::lean_inc(v_head_4472_);
                v___x_4477_ = leanh::lean_apply_1(v_p_4470_, v_head_4472_);
                v___x_4478_ = (leanh::lean_unbox(v___x_4477_) as u8);
                if v___x_4478_ == 0 {
                    leanh::lean_del_object(v___x_4475_);
                    leanh::lean_dec(v_tail_4473_);
                    leanh::lean_dec(v_head_4472_);
                    leanh::lean_dec_ref(v_p_4470_);
                    v___x_4479_ = leanh::lean_box(0);
                    return v___x_4479_;
                } else {
                    v___x_4480_ = l_List_takeWhile___redArg(v_p_4470_, v_tail_4473_);
                    if v_isShared_4476_ == 0 {
                        leanh::lean_ctor_set(v___x_4475_, 1, v___x_4480_);
                        v___x_4482_ = v___x_4475_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_head_4472_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___x_4480_);
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
    mut v_00_u03b1_4485_: *mut leanh::LeanObject,
    mut v_p_4486_: *mut leanh::LeanObject,
    mut v_x_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = l_List_takeWhile___redArg(v_p_4486_, v_x_4487_);
    return v___x_4488_;
}
pub unsafe fn l_List_dropWhile___redArg(
    mut v_p_4489_: *mut leanh::LeanObject,
    mut v_x_4490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4490_) == 0 {
                    leanh::lean_dec_ref(v_p_4489_);
                    return v_x_4490_;
                } else {
                    v_head_4491_ = leanh::lean_ctor_get(v_x_4490_, 0);
                    v_tail_4492_ = leanh::lean_ctor_get(v_x_4490_, 1);
                    leanh::lean_inc_ref(v_p_4489_);
                    leanh::lean_inc(v_head_4491_);
                    v___x_4493_ = leanh::lean_apply_1(v_p_4489_, v_head_4491_);
                    v___x_4494_ = (leanh::lean_unbox(v___x_4493_) as u8);
                    if v___x_4494_ == 0 {
                        leanh::lean_dec_ref(v_p_4489_);
                        return v_x_4490_;
                    } else {
                        leanh::lean_inc(v_tail_4492_);
                        leanh::lean_dec_ref_known(v_x_4490_, 2);
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
    mut v_00_u03b1_4496_: *mut leanh::LeanObject,
    mut v_p_4497_: *mut leanh::LeanObject,
    mut v_x_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4499_ = l_List_dropWhile___redArg(v_p_4497_, v_x_4498_);
    return v___x_4499_;
}
pub unsafe fn l_List_partition_loop___redArg(
    mut v_p_4500_: *mut leanh::LeanObject,
    mut v_a_4501_: *mut leanh::LeanObject,
    mut v_a_4502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_head_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v_fst_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_isSharedCheck_4541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4501_) == 0 {
                    leanh::lean_dec_ref(v_p_4500_);
                    v_fst_4503_ = leanh::lean_ctor_get(v_a_4502_, 0);
                    v_snd_4504_ = leanh::lean_ctor_get(v_a_4502_, 1);
                    v_isSharedCheck_4513_ = (!leanh::lean_is_exclusive(v_a_4502_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4506_ = v_a_4502_;
                        v_isShared_4507_ = v_isSharedCheck_4513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4504_);
                        leanh::lean_inc(v_fst_4503_);
                        leanh::lean_dec(v_a_4502_);
                        v___x_4506_ = leanh::lean_box(0);
                        v_isShared_4507_ = v_isSharedCheck_4513_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_4514_ = leanh::lean_ctor_get(v_a_4501_, 0);
                    v_tail_4515_ = leanh::lean_ctor_get(v_a_4501_, 1);
                    v_isSharedCheck_4541_ = (!leanh::lean_is_exclusive(v_a_4501_)) as u8;
                    if v_isSharedCheck_4541_ == 0 {
                        v___x_4517_ = v_a_4501_;
                        v_isShared_4518_ = v_isSharedCheck_4541_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4515_);
                        leanh::lean_inc(v_head_4514_);
                        leanh::lean_dec(v_a_4501_);
                        v___x_4517_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4506_, 1, v___x_4509_);
                    leanh::lean_ctor_set(v___x_4506_, 0, v___x_4508_);
                    v___x_4511_ = v___x_4506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 1, v___x_4509_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4511_;
            }
            3 => {
                v_fst_4519_ = leanh::lean_ctor_get(v_a_4502_, 0);
                v_snd_4520_ = leanh::lean_ctor_get(v_a_4502_, 1);
                v_isSharedCheck_4540_ = (!leanh::lean_is_exclusive(v_a_4502_)) as u8;
                if v_isSharedCheck_4540_ == 0 {
                    v___x_4522_ = v_a_4502_;
                    v_isShared_4523_ = v_isSharedCheck_4540_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4520_);
                    leanh::lean_inc(v_fst_4519_);
                    leanh::lean_dec(v_a_4502_);
                    v___x_4522_ = leanh::lean_box(0);
                    v_isShared_4523_ = v_isSharedCheck_4540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_p_4500_);
                leanh::lean_inc(v_head_4514_);
                v___x_4524_ = leanh::lean_apply_1(v_p_4500_, v_head_4514_);
                v___x_4525_ = (leanh::lean_unbox(v___x_4524_) as u8);
                if v___x_4525_ == 0 {
                    if v_isShared_4518_ == 0 {
                        leanh::lean_ctor_set(v___x_4517_, 1, v_snd_4520_);
                        v___x_4527_ = v___x_4517_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4532_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_head_4514_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_snd_4520_);
                        v___x_4527_ = v_reuseFailAlloc_4532_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4518_ == 0 {
                        leanh::lean_ctor_set(v___x_4517_, 1, v_fst_4519_);
                        v___x_4534_ = v___x_4517_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4539_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_head_4514_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_fst_4519_);
                        v___x_4534_ = v_reuseFailAlloc_4539_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4523_ == 0 {
                    leanh::lean_ctor_set(v___x_4522_, 1, v___x_4527_);
                    v___x_4529_ = v___x_4522_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_fst_4519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___x_4527_);
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
                    leanh::lean_ctor_set(v___x_4522_, 0, v___x_4534_);
                    v___x_4536_ = v___x_4522_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4538_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_snd_4520_);
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
    mut v_00_u03b1_4542_: *mut leanh::LeanObject,
    mut v_p_4543_: *mut leanh::LeanObject,
    mut v_a_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4546_ = l_List_partition_loop___redArg(v_p_4543_, v_a_4544_, v_a_4545_);
    return v___x_4546_;
}
pub unsafe fn l_List_partition___redArg(
    mut v_p_4549_: *mut leanh::LeanObject,
    mut v_as_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_List_partition___redArg___closed__0;
    v___x_4552_ = l_List_partition_loop___redArg(v_p_4549_, v_as_4550_, v___x_4551_);
    return v___x_4552_;
}
pub unsafe fn l_List_partition(
    mut v_00_u03b1_4553_: *mut leanh::LeanObject,
    mut v_p_4554_: *mut leanh::LeanObject,
    mut v_as_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_List_partition___redArg___closed__0;
    v___x_4557_ = l_List_partition_loop___redArg(v_p_4554_, v_as_4555_, v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn l_List_dropLast___redArg(
    mut v_x_4558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_unused_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4558_) == 0 {
                    return v_x_4558_;
                } else {
                    v_tail_4559_ = leanh::lean_ctor_get(v_x_4558_, 1);
                    leanh::lean_inc(v_tail_4559_);
                    if leanh::lean_obj_tag(v_tail_4559_) == 0 {
                        leanh::lean_dec_ref_known(v_x_4558_, 2);
                        return v_tail_4559_;
                    } else {
                        v_head_4560_ = leanh::lean_ctor_get(v_x_4558_, 0);
                        v_isSharedCheck_4568_ = (!leanh::lean_is_exclusive(v_x_4558_)) as u8;
                        if v_isSharedCheck_4568_ == 0 {
                            v_unused_4569_ = leanh::lean_ctor_get(v_x_4558_, 1);
                            leanh::lean_dec(v_unused_4569_);
                            v___x_4562_ = v_x_4558_;
                            v_isShared_4563_ = v_isSharedCheck_4568_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_4560_);
                            leanh::lean_dec(v_x_4558_);
                            v___x_4562_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4562_, 1, v___x_4564_);
                    v___x_4566_ = v___x_4562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_head_4560_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 1, v___x_4564_);
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
    mut v_00_u03b1_4570_: *mut leanh::LeanObject,
    mut v_x_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = l_List_dropLast___redArg(v_x_4571_);
    return v___x_4572_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter___redArg(
    mut v_x_4573_: *mut leanh::LeanObject,
    mut v_h__1_4574_: *mut leanh::LeanObject,
    mut v_h__2_4575_: *mut leanh::LeanObject,
    mut v_h__3_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4573_) == 0 {
        let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_4576_);
        leanh::lean_dec(v_h__2_4575_);
        v___x_4577_ = leanh::lean_box(0);
        v___x_4578_ = leanh::lean_apply_1(v_h__1_4574_, v___x_4577_);
        return v___x_4578_;
    } else {
        let mut v_tail_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4574_);
        v_tail_4579_ = leanh::lean_ctor_get(v_x_4573_, 1);
        if leanh::lean_obj_tag(v_tail_4579_) == 0 {
            let mut v_head_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_4576_);
            v_head_4580_ = leanh::lean_ctor_get(v_x_4573_, 0);
            leanh::lean_inc(v_head_4580_);
            leanh::lean_dec_ref_known(v_x_4573_, 2);
            v___x_4581_ = leanh::lean_apply_1(v_h__2_4575_, v_head_4580_);
            return v___x_4581_;
        } else {
            let mut v_head_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_4579_);
            leanh::lean_dec(v_h__2_4575_);
            v_head_4582_ = leanh::lean_ctor_get(v_x_4573_, 0);
            leanh::lean_inc(v_head_4582_);
            leanh::lean_dec_ref_known(v_x_4573_, 2);
            v___x_4583_ = leanh::lean_apply_3(
                v_h__3_4576_,
                v_head_4582_,
                v_tail_4579_,
                leanh::lean_box(0),
            );
            return v___x_4583_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_dropLast_match__1_splitter(
    mut v_00_u03b1_4584_: *mut leanh::LeanObject,
    mut v_motive_4585_: *mut leanh::LeanObject,
    mut v_x_4586_: *mut leanh::LeanObject,
    mut v_h__1_4587_: *mut leanh::LeanObject,
    mut v_h__2_4588_: *mut leanh::LeanObject,
    mut v_h__3_4589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4586_) == 0 {
        let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_4589_);
        leanh::lean_dec(v_h__2_4588_);
        v___x_4590_ = leanh::lean_box(0);
        v___x_4591_ = leanh::lean_apply_1(v_h__1_4587_, v___x_4590_);
        return v___x_4591_;
    } else {
        let mut v_tail_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4587_);
        v_tail_4592_ = leanh::lean_ctor_get(v_x_4586_, 1);
        if leanh::lean_obj_tag(v_tail_4592_) == 0 {
            let mut v_head_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_4589_);
            v_head_4593_ = leanh::lean_ctor_get(v_x_4586_, 0);
            leanh::lean_inc(v_head_4593_);
            leanh::lean_dec_ref_known(v_x_4586_, 2);
            v___x_4594_ = leanh::lean_apply_1(v_h__2_4588_, v_head_4593_);
            return v___x_4594_;
        } else {
            let mut v_head_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_4592_);
            leanh::lean_dec(v_h__2_4588_);
            v_head_4595_ = leanh::lean_ctor_get(v_x_4586_, 0);
            leanh::lean_inc(v_head_4595_);
            leanh::lean_dec_ref_known(v_x_4586_, 2);
            v___x_4596_ = leanh::lean_apply_3(
                v_h__3_4589_,
                v_head_4595_,
                v_tail_4592_,
                leanh::lean_box(0),
            );
            return v___x_4596_;
        }
    }
}
pub unsafe fn l_List_instHasSubset(
    mut v_00_u03b1_4597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4598_ = leanh::lean_box(0);
    return v___x_4598_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(
    mut v___f_4599_: *mut leanh::LeanObject,
    mut v_x_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4602_: u8 = 0;
    v___x_4602_ = l_List_elem___redArg(v___f_4599_, v_a_4601_, v_x_4600_);
    return v___x_4602_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed(
    mut v___f_4603_: *mut leanh::LeanObject,
    mut v_x_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4606_: u8 = 0;
    let mut v_r_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0(
        v___f_4603_,
        v_x_4604_,
        v_a_4605_,
    );
    v_r_4607_ = leanh::lean_box((v_res_4606_) as usize);
    return v_r_4607_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg(
    mut v_inst_4608_: *mut leanh::LeanObject,
    mut v_x_4609_: *mut leanh::LeanObject,
    mut v_x_4610_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    v___f_4611_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4611_, 0, v_inst_4608_);
    v___f_4612_ = leanh::lean_alloc_closure(
        l_List_instDecidableRelSubsetOfDecidableEq___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4612_, 0, v___f_4611_);
    leanh::lean_closure_set(v___f_4612_, 1, v_x_4610_);
    v___x_4613_ = l_List_decidableBAll___redArg(v___f_4612_, v_x_4609_);
    return v___x_4613_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___redArg___boxed(
    mut v_inst_4614_: *mut leanh::LeanObject,
    mut v_x_4615_: *mut leanh::LeanObject,
    mut v_x_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4617_: u8 = 0;
    let mut v_r_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ =
        l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_4614_, v_x_4615_, v_x_4616_);
    v_r_4618_ = leanh::lean_box((v_res_4617_) as usize);
    return v_r_4618_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq(
    mut v_00_u03b1_4619_: *mut leanh::LeanObject,
    mut v_inst_4620_: *mut leanh::LeanObject,
    mut v_x_4621_: *mut leanh::LeanObject,
    mut v_x_4622_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4623_: u8 = 0;
    v___x_4623_ =
        l_List_instDecidableRelSubsetOfDecidableEq___redArg(v_inst_4620_, v_x_4621_, v_x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_List_instDecidableRelSubsetOfDecidableEq___boxed(
    mut v_00_u03b1_4624_: *mut leanh::LeanObject,
    mut v_inst_4625_: *mut leanh::LeanObject,
    mut v_x_4626_: *mut leanh::LeanObject,
    mut v_x_4627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4628_: u8 = 0;
    let mut v_r_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4628_ = l_List_instDecidableRelSubsetOfDecidableEq(
        v_00_u03b1_4624_,
        v_inst_4625_,
        v_x_4626_,
        v_x_4627_,
    );
    v_r_4629_ = leanh::lean_box((v_res_4628_) as usize);
    return v_r_4629_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__2;
    v___x_4664_ = l_String_toRawSubstring_x27(v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(
    mut v_x_4684_: *mut leanh::LeanObject,
    mut v_a_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    v___x_4687_ = l_List_term___x3c_x2b___00__closed__2;
    leanh::lean_inc(v_x_4684_);
    v___x_4688_ = l_Lean_Syntax_isOfKind(v_x_4684_, v___x_4687_);
    if v___x_4688_ == 0 {
        let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4684_);
        v___x_4689_ = leanh::lean_box(1);
        v___x_4690_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
        leanh::lean_ctor_set(v___x_4690_, 1, v_a_4686_);
        return v___x_4690_;
    } else {
        let mut v_quotContext_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4698_: u8 = 0;
        let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4691_ = leanh::lean_ctor_get(v_a_4685_, 1);
        v_currMacroScope_4692_ = leanh::lean_ctor_get(v_a_4685_, 2);
        v_ref_4693_ = leanh::lean_ctor_get(v_a_4685_, 5);
        v___x_4694_ = leanh::lean_unsigned_to_nat(0);
        v___x_4695_ = l_Lean_Syntax_getArg(v_x_4684_, v___x_4694_);
        v___x_4696_ = leanh::lean_unsigned_to_nat(2);
        v___x_4697_ = l_Lean_Syntax_getArg(v_x_4684_, v___x_4696_);
        leanh::lean_dec(v_x_4684_);
        v___x_4698_ = 0;
        v___x_4699_ = l_Lean_SourceInfo_fromRef(v_ref_4693_, v___x_4698_);
        v___x_4700_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_4701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__3);
        v___x_4702_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__4;
        leanh::lean_inc(v_currMacroScope_4692_);
        leanh::lean_inc(v_quotContext_4691_);
        v___x_4703_ =
            l_Lean_addMacroScope(v_quotContext_4691_, v___x_4702_, v_currMacroScope_4692_);
        v___x_4704_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__10;
        leanh::lean_inc_n(v___x_4699_, 2);
        v___x_4705_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_4705_, 0, v___x_4699_);
        leanh::lean_ctor_set(v___x_4705_, 1, v___x_4701_);
        leanh::lean_ctor_set(v___x_4705_, 2, v___x_4703_);
        leanh::lean_ctor_set(v___x_4705_, 3, v___x_4704_);
        v___x_4706_ = l_List_lex___auto__1___closed__9;
        v___x_4707_ = l_Lean_Syntax_node2(v___x_4699_, v___x_4706_, v___x_4695_, v___x_4697_);
        v___x_4708_ = l_Lean_Syntax_node2(v___x_4699_, v___x_4700_, v___x_4705_, v___x_4707_);
        v___x_4709_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4709_, 0, v___x_4708_);
        leanh::lean_ctor_set(v___x_4709_, 1, v_a_4686_);
        return v___x_4709_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___boxed(
    mut v_x_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4713_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1(
        v_x_4710_, v_a_4711_, v_a_4712_,
    );
    leanh::lean_dec_ref(v_a_4711_);
    return v_res_4713_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(
    mut v_x_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: u8 = 0;
    v___x_4720_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    leanh::lean_inc(v_x_4717_);
    v___x_4721_ = l_Lean_Syntax_isOfKind(v_x_4717_, v___x_4720_);
    if v___x_4721_ == 0 {
        let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4717_);
        v___x_4722_ = leanh::lean_box(0);
        v___x_4723_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4723_, 0, v___x_4722_);
        leanh::lean_ctor_set(v___x_4723_, 1, v_a_4719_);
        return v___x_4723_;
    } else {
        let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: u8 = 0;
        v___x_4724_ = leanh::lean_unsigned_to_nat(0);
        v___x_4725_ = l_Lean_Syntax_getArg(v_x_4717_, v___x_4724_);
        v___x_4726_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        leanh::lean_inc(v___x_4725_);
        v___x_4727_ = l_Lean_Syntax_isOfKind(v___x_4725_, v___x_4726_);
        if v___x_4727_ == 0 {
            let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4725_);
            leanh::lean_dec(v_x_4717_);
            v___x_4728_ = leanh::lean_box(0);
            v___x_4729_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4729_, 0, v___x_4728_);
            leanh::lean_ctor_set(v___x_4729_, 1, v_a_4719_);
            return v___x_4729_;
        } else {
            let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4733_: u8 = 0;
            v___x_4730_ = leanh::lean_unsigned_to_nat(1);
            v___x_4731_ = l_Lean_Syntax_getArg(v_x_4717_, v___x_4730_);
            leanh::lean_dec(v_x_4717_);
            v___x_4732_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_4731_);
            v___x_4733_ = l_Lean_Syntax_matchesNull(v___x_4731_, v___x_4732_);
            if v___x_4733_ == 0 {
                let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_4731_);
                leanh::lean_dec(v___x_4725_);
                v___x_4734_ = leanh::lean_box(0);
                v___x_4735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4735_, 0, v___x_4734_);
                leanh::lean_ctor_set(v___x_4735_, 1, v_a_4719_);
                return v___x_4735_;
            } else {
                let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4739_: u8 = 0;
                let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4736_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4724_);
                v___x_4737_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4730_);
                leanh::lean_dec(v___x_4731_);
                v_ref_4738_ = l_Lean_replaceRef(v___x_4725_, v_a_4718_);
                leanh::lean_dec(v___x_4725_);
                v___x_4739_ = 0;
                v___x_4740_ = l_Lean_SourceInfo_fromRef(v_ref_4738_, v___x_4739_);
                leanh::lean_dec(v_ref_4738_);
                v___x_4741_ = l_List_term___x3c_x2b___00__closed__2;
                v___x_4742_ = l_List_term___x3c_x2b___00__closed__5;
                leanh::lean_inc(v___x_4740_);
                v___x_4743_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4743_, 0, v___x_4740_);
                leanh::lean_ctor_set(v___x_4743_, 1, v___x_4742_);
                v___x_4744_ = l_Lean_Syntax_node3(
                    v___x_4740_,
                    v___x_4741_,
                    v___x_4736_,
                    v___x_4743_,
                    v___x_4737_,
                );
                v___x_4745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4745_, 0, v___x_4744_);
                leanh::lean_ctor_set(v___x_4745_, 1, v_a_4719_);
                return v___x_4745_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___boxed(
    mut v_x_4746_: *mut leanh::LeanObject,
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_a_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4749_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1(
        v_x_4746_, v_a_4747_, v_a_4748_,
    );
    leanh::lean_dec(v_a_4747_);
    return v_res_4749_;
}
pub unsafe fn l_List_isSublist___redArg(
    mut v_inst_4750_: *mut leanh::LeanObject,
    mut v_x_4751_: *mut leanh::LeanObject,
    mut v_x_4752_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: u8 = 0;
    let mut v_head_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4751_) == 0 {
                    leanh::lean_dec(v_x_4752_);
                    leanh::lean_dec_ref(v_inst_4750_);
                    v___x_4753_ = 1;
                    return v___x_4753_;
                } else {
                    if leanh::lean_obj_tag(v_x_4752_) == 0 {
                        leanh::lean_dec_ref_known(v_x_4751_, 2);
                        leanh::lean_dec_ref(v_inst_4750_);
                        v___x_4754_ = 0;
                        return v___x_4754_;
                    } else {
                        v_head_4755_ = leanh::lean_ctor_get(v_x_4751_, 0);
                        v_tail_4756_ = leanh::lean_ctor_get(v_x_4751_, 1);
                        v_head_4757_ = leanh::lean_ctor_get(v_x_4752_, 0);
                        leanh::lean_inc(v_head_4757_);
                        v_tail_4758_ = leanh::lean_ctor_get(v_x_4752_, 1);
                        leanh::lean_inc(v_tail_4758_);
                        leanh::lean_dec_ref_known(v_x_4752_, 2);
                        leanh::lean_inc_ref(v_inst_4750_);
                        leanh::lean_inc(v_head_4755_);
                        v___x_4759_ =
                            leanh::lean_apply_2(v_inst_4750_, v_head_4755_, v_head_4757_);
                        v___x_4760_ = (leanh::lean_unbox(v___x_4759_) as u8);
                        if v___x_4760_ == 0 {
                            v_x_4752_ = v_tail_4758_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_4756_);
                            leanh::lean_dec_ref_known(v_x_4751_, 2);
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
    mut v_inst_4763_: *mut leanh::LeanObject,
    mut v_x_4764_: *mut leanh::LeanObject,
    mut v_x_4765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4766_: u8 = 0;
    let mut v_r_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ = l_List_isSublist___redArg(v_inst_4763_, v_x_4764_, v_x_4765_);
    v_r_4767_ = leanh::lean_box((v_res_4766_) as usize);
    return v_r_4767_;
}
pub unsafe fn l_List_isSublist(
    mut v_00_u03b1_4768_: *mut leanh::LeanObject,
    mut v_inst_4769_: *mut leanh::LeanObject,
    mut v_x_4770_: *mut leanh::LeanObject,
    mut v_x_4771_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4772_: u8 = 0;
    v___x_4772_ = l_List_isSublist___redArg(v_inst_4769_, v_x_4770_, v_x_4771_);
    return v___x_4772_;
}
pub unsafe fn l_List_isSublist___boxed(
    mut v_00_u03b1_4773_: *mut leanh::LeanObject,
    mut v_inst_4774_: *mut leanh::LeanObject,
    mut v_x_4775_: *mut leanh::LeanObject,
    mut v_x_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4777_: u8 = 0;
    let mut v_r_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4777_ = l_List_isSublist(v_00_u03b1_4773_, v_inst_4774_, v_x_4775_, v_x_4776_);
    v_r_4778_ = leanh::lean_box((v_res_4777_) as usize);
    return v_r_4778_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__0;
    v___x_4797_ = l_String_toRawSubstring_x27(v___x_4796_);
    return v___x_4797_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(
    mut v_x_4809_: *mut leanh::LeanObject,
    mut v_a_4810_: *mut leanh::LeanObject,
    mut v_a_4811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: u8 = 0;
    v___x_4812_ = l_List_term___x3c_x2b_x3a___00__closed__1;
    leanh::lean_inc(v_x_4809_);
    v___x_4813_ = l_Lean_Syntax_isOfKind(v_x_4809_, v___x_4812_);
    if v___x_4813_ == 0 {
        let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4809_);
        v___x_4814_ = leanh::lean_box(1);
        v___x_4815_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4815_, 0, v___x_4814_);
        leanh::lean_ctor_set(v___x_4815_, 1, v_a_4811_);
        return v___x_4815_;
    } else {
        let mut v_quotContext_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: u8 = 0;
        let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4816_ = leanh::lean_ctor_get(v_a_4810_, 1);
        v_currMacroScope_4817_ = leanh::lean_ctor_get(v_a_4810_, 2);
        v_ref_4818_ = leanh::lean_ctor_get(v_a_4810_, 5);
        v___x_4819_ = leanh::lean_unsigned_to_nat(0);
        v___x_4820_ = l_Lean_Syntax_getArg(v_x_4809_, v___x_4819_);
        v___x_4821_ = leanh::lean_unsigned_to_nat(2);
        v___x_4822_ = l_Lean_Syntax_getArg(v_x_4809_, v___x_4821_);
        leanh::lean_dec(v_x_4809_);
        v___x_4823_ = 0;
        v___x_4824_ = l_Lean_SourceInfo_fromRef(v_ref_4818_, v___x_4823_);
        v___x_4825_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_4826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__1);
        v___x_4827_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__2;
        leanh::lean_inc(v_currMacroScope_4817_);
        leanh::lean_inc(v_quotContext_4816_);
        v___x_4828_ =
            l_Lean_addMacroScope(v_quotContext_4816_, v___x_4827_, v_currMacroScope_4817_);
        v___x_4829_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___closed__5;
        leanh::lean_inc_n(v___x_4824_, 2);
        v___x_4830_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_4830_, 0, v___x_4824_);
        leanh::lean_ctor_set(v___x_4830_, 1, v___x_4826_);
        leanh::lean_ctor_set(v___x_4830_, 2, v___x_4828_);
        leanh::lean_ctor_set(v___x_4830_, 3, v___x_4829_);
        v___x_4831_ = l_List_lex___auto__1___closed__9;
        v___x_4832_ = l_Lean_Syntax_node2(v___x_4824_, v___x_4831_, v___x_4820_, v___x_4822_);
        v___x_4833_ = l_Lean_Syntax_node2(v___x_4824_, v___x_4825_, v___x_4830_, v___x_4832_);
        v___x_4834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4834_, 0, v___x_4833_);
        leanh::lean_ctor_set(v___x_4834_, 1, v_a_4811_);
        return v___x_4834_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1___boxed(
    mut v_x_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_a_4837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b_x3a____1(
            v_x_4835_, v_a_4836_, v_a_4837_,
        );
    leanh::lean_dec_ref(v_a_4836_);
    return v_res_4838_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(
    mut v_x_4839_: *mut leanh::LeanObject,
    mut v_a_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    v___x_4842_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    leanh::lean_inc(v_x_4839_);
    v___x_4843_ = l_Lean_Syntax_isOfKind(v_x_4839_, v___x_4842_);
    if v___x_4843_ == 0 {
        let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_4839_);
        v___x_4844_ = leanh::lean_box(0);
        v___x_4845_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4845_, 0, v___x_4844_);
        leanh::lean_ctor_set(v___x_4845_, 1, v_a_4841_);
        return v___x_4845_;
    } else {
        let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: u8 = 0;
        v___x_4846_ = leanh::lean_unsigned_to_nat(0);
        v___x_4847_ = l_Lean_Syntax_getArg(v_x_4839_, v___x_4846_);
        v___x_4848_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        leanh::lean_inc(v___x_4847_);
        v___x_4849_ = l_Lean_Syntax_isOfKind(v___x_4847_, v___x_4848_);
        if v___x_4849_ == 0 {
            let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4847_);
            leanh::lean_dec(v_x_4839_);
            v___x_4850_ = leanh::lean_box(0);
            v___x_4851_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4851_, 0, v___x_4850_);
            leanh::lean_ctor_set(v___x_4851_, 1, v_a_4841_);
            return v___x_4851_;
        } else {
            let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4855_: u8 = 0;
            v___x_4852_ = leanh::lean_unsigned_to_nat(1);
            v___x_4853_ = l_Lean_Syntax_getArg(v_x_4839_, v___x_4852_);
            leanh::lean_dec(v_x_4839_);
            v___x_4854_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_4853_);
            v___x_4855_ = l_Lean_Syntax_matchesNull(v___x_4853_, v___x_4854_);
            if v___x_4855_ == 0 {
                let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_4853_);
                leanh::lean_dec(v___x_4847_);
                v___x_4856_ = leanh::lean_box(0);
                v___x_4857_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4857_, 0, v___x_4856_);
                leanh::lean_ctor_set(v___x_4857_, 1, v_a_4841_);
                return v___x_4857_;
            } else {
                let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4861_: u8 = 0;
                let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4858_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4846_);
                v___x_4859_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4852_);
                leanh::lean_dec(v___x_4853_);
                v_ref_4860_ = l_Lean_replaceRef(v___x_4847_, v_a_4840_);
                leanh::lean_dec(v___x_4847_);
                v___x_4861_ = 0;
                v___x_4862_ = l_Lean_SourceInfo_fromRef(v_ref_4860_, v___x_4861_);
                leanh::lean_dec(v_ref_4860_);
                v___x_4863_ = l_List_term___x3c_x2b_x3a___00__closed__1;
                v___x_4864_ = l_List_term___x3c_x2b_x3a___00__closed__2;
                leanh::lean_inc(v___x_4862_);
                v___x_4865_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4865_, 0, v___x_4862_);
                leanh::lean_ctor_set(v___x_4865_, 1, v___x_4864_);
                v___x_4866_ = l_Lean_Syntax_node3(
                    v___x_4862_,
                    v___x_4863_,
                    v___x_4858_,
                    v___x_4865_,
                    v___x_4859_,
                );
                v___x_4867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4867_, 0, v___x_4866_);
                leanh::lean_ctor_set(v___x_4867_, 1, v_a_4841_);
                return v___x_4867_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1___boxed(
    mut v_x_4868_: *mut leanh::LeanObject,
    mut v_a_4869_: *mut leanh::LeanObject,
    mut v_a_4870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsPrefix__1(
        v_x_4868_, v_a_4869_, v_a_4870_,
    );
    leanh::lean_dec(v_a_4869_);
    return v_res_4871_;
}
pub unsafe fn l_List_isPrefixOf___redArg(
    mut v_inst_4872_: *mut leanh::LeanObject,
    mut v_x_4873_: *mut leanh::LeanObject,
    mut v_x_4874_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: u8 = 0;
    let mut v_head_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4873_) == 0 {
                    leanh::lean_dec(v_x_4874_);
                    leanh::lean_dec_ref(v_inst_4872_);
                    v___x_4875_ = 1;
                    return v___x_4875_;
                } else {
                    if leanh::lean_obj_tag(v_x_4874_) == 0 {
                        leanh::lean_dec_ref_known(v_x_4873_, 2);
                        leanh::lean_dec_ref(v_inst_4872_);
                        v___x_4876_ = 0;
                        return v___x_4876_;
                    } else {
                        v_head_4877_ = leanh::lean_ctor_get(v_x_4873_, 0);
                        leanh::lean_inc(v_head_4877_);
                        v_tail_4878_ = leanh::lean_ctor_get(v_x_4873_, 1);
                        leanh::lean_inc(v_tail_4878_);
                        leanh::lean_dec_ref_known(v_x_4873_, 2);
                        v_head_4879_ = leanh::lean_ctor_get(v_x_4874_, 0);
                        leanh::lean_inc(v_head_4879_);
                        v_tail_4880_ = leanh::lean_ctor_get(v_x_4874_, 1);
                        leanh::lean_inc(v_tail_4880_);
                        leanh::lean_dec_ref_known(v_x_4874_, 2);
                        leanh::lean_inc_ref(v_inst_4872_);
                        v___x_4881_ =
                            leanh::lean_apply_2(v_inst_4872_, v_head_4877_, v_head_4879_);
                        v___x_4882_ = (leanh::lean_unbox(v___x_4881_) as u8);
                        if v___x_4882_ == 0 {
                            leanh::lean_dec(v_tail_4880_);
                            leanh::lean_dec(v_tail_4878_);
                            leanh::lean_dec_ref(v_inst_4872_);
                            v___x_4883_ = (leanh::lean_unbox(v___x_4881_) as u8);
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
    mut v_inst_4885_: *mut leanh::LeanObject,
    mut v_x_4886_: *mut leanh::LeanObject,
    mut v_x_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4888_: u8 = 0;
    let mut v_r_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4888_ = l_List_isPrefixOf___redArg(v_inst_4885_, v_x_4886_, v_x_4887_);
    v_r_4889_ = leanh::lean_box((v_res_4888_) as usize);
    return v_r_4889_;
}
pub unsafe fn l_List_isPrefixOf(
    mut v_00_u03b1_4890_: *mut leanh::LeanObject,
    mut v_inst_4891_: *mut leanh::LeanObject,
    mut v_x_4892_: *mut leanh::LeanObject,
    mut v_x_4893_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4894_: u8 = 0;
    v___x_4894_ = l_List_isPrefixOf___redArg(v_inst_4891_, v_x_4892_, v_x_4893_);
    return v___x_4894_;
}
pub unsafe fn l_List_isPrefixOf___boxed(
    mut v_00_u03b1_4895_: *mut leanh::LeanObject,
    mut v_inst_4896_: *mut leanh::LeanObject,
    mut v_x_4897_: *mut leanh::LeanObject,
    mut v_x_4898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4899_: u8 = 0;
    let mut v_r_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4899_ = l_List_isPrefixOf(v_00_u03b1_4895_, v_inst_4896_, v_x_4897_, v_x_4898_);
    v_r_4900_ = leanh::lean_box((v_res_4899_) as usize);
    return v_r_4900_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_isPrefixOf_match__1_splitter___redArg(
    mut v_x_4901_: *mut leanh::LeanObject,
    mut v_x_4902_: *mut leanh::LeanObject,
    mut v_h__1_4903_: *mut leanh::LeanObject,
    mut v_h__2_4904_: *mut leanh::LeanObject,
    mut v_h__3_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4901_) == 0 {
        let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_4905_);
        leanh::lean_dec(v_h__2_4904_);
        v___x_4906_ = leanh::lean_apply_1(v_h__1_4903_, v_x_4902_);
        return v___x_4906_;
    } else {
        leanh::lean_dec(v_h__1_4903_);
        if leanh::lean_obj_tag(v_x_4902_) == 0 {
            let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_4905_);
            v___x_4907_ =
                leanh::lean_apply_2(v_h__2_4904_, v_x_4901_, leanh::lean_box(0));
            return v___x_4907_;
        } else {
            let mut v_head_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_4904_);
            v_head_4908_ = leanh::lean_ctor_get(v_x_4901_, 0);
            leanh::lean_inc(v_head_4908_);
            v_tail_4909_ = leanh::lean_ctor_get(v_x_4901_, 1);
            leanh::lean_inc(v_tail_4909_);
            leanh::lean_dec_ref_known(v_x_4901_, 2);
            v_head_4910_ = leanh::lean_ctor_get(v_x_4902_, 0);
            leanh::lean_inc(v_head_4910_);
            v_tail_4911_ = leanh::lean_ctor_get(v_x_4902_, 1);
            leanh::lean_inc(v_tail_4911_);
            leanh::lean_dec_ref_known(v_x_4902_, 2);
            v___x_4912_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_4913_: *mut leanh::LeanObject,
    mut v_motive_4914_: *mut leanh::LeanObject,
    mut v_x_4915_: *mut leanh::LeanObject,
    mut v_x_4916_: *mut leanh::LeanObject,
    mut v_h__1_4917_: *mut leanh::LeanObject,
    mut v_h__2_4918_: *mut leanh::LeanObject,
    mut v_h__3_4919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4915_) == 0 {
        let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_4919_);
        leanh::lean_dec(v_h__2_4918_);
        v___x_4920_ = leanh::lean_apply_1(v_h__1_4917_, v_x_4916_);
        return v___x_4920_;
    } else {
        leanh::lean_dec(v_h__1_4917_);
        if leanh::lean_obj_tag(v_x_4916_) == 0 {
            let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_4919_);
            v___x_4921_ =
                leanh::lean_apply_2(v_h__2_4918_, v_x_4915_, leanh::lean_box(0));
            return v___x_4921_;
        } else {
            let mut v_head_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_4918_);
            v_head_4922_ = leanh::lean_ctor_get(v_x_4915_, 0);
            leanh::lean_inc(v_head_4922_);
            v_tail_4923_ = leanh::lean_ctor_get(v_x_4915_, 1);
            leanh::lean_inc(v_tail_4923_);
            leanh::lean_dec_ref_known(v_x_4915_, 2);
            v_head_4924_ = leanh::lean_ctor_get(v_x_4916_, 0);
            leanh::lean_inc(v_head_4924_);
            v_tail_4925_ = leanh::lean_ctor_get(v_x_4916_, 1);
            leanh::lean_inc(v_tail_4925_);
            leanh::lean_dec_ref_known(v_x_4916_, 2);
            v___x_4926_ = leanh::lean_apply_4(
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
    mut v_inst_4927_: *mut leanh::LeanObject,
    mut v_x_4928_: *mut leanh::LeanObject,
    mut v_x_4929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: u8 = 0;
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4928_) == 0 {
                    leanh::lean_dec_ref(v_inst_4927_);
                    v___x_4930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4930_, 0, v_x_4929_);
                    return v___x_4930_;
                } else {
                    if leanh::lean_obj_tag(v_x_4929_) == 0 {
                        leanh::lean_dec_ref_known(v_x_4928_, 2);
                        leanh::lean_dec_ref(v_inst_4927_);
                        v___x_4931_ = leanh::lean_box(0);
                        return v___x_4931_;
                    } else {
                        v_head_4932_ = leanh::lean_ctor_get(v_x_4928_, 0);
                        leanh::lean_inc(v_head_4932_);
                        v_tail_4933_ = leanh::lean_ctor_get(v_x_4928_, 1);
                        leanh::lean_inc(v_tail_4933_);
                        leanh::lean_dec_ref_known(v_x_4928_, 2);
                        v_head_4934_ = leanh::lean_ctor_get(v_x_4929_, 0);
                        leanh::lean_inc(v_head_4934_);
                        v_tail_4935_ = leanh::lean_ctor_get(v_x_4929_, 1);
                        leanh::lean_inc(v_tail_4935_);
                        leanh::lean_dec_ref_known(v_x_4929_, 2);
                        leanh::lean_inc_ref(v_inst_4927_);
                        v___x_4936_ =
                            leanh::lean_apply_2(v_inst_4927_, v_head_4932_, v_head_4934_);
                        v___x_4937_ = (leanh::lean_unbox(v___x_4936_) as u8);
                        if v___x_4937_ == 0 {
                            leanh::lean_dec(v_tail_4935_);
                            leanh::lean_dec(v_tail_4933_);
                            leanh::lean_dec_ref(v_inst_4927_);
                            v___x_4938_ = leanh::lean_box(0);
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
    mut v_00_u03b1_4940_: *mut leanh::LeanObject,
    mut v_inst_4941_: *mut leanh::LeanObject,
    mut v_x_4942_: *mut leanh::LeanObject,
    mut v_x_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4944_ = l_List_isPrefixOf_x3f___redArg(v_inst_4941_, v_x_4942_, v_x_4943_);
    return v___x_4944_;
}
pub unsafe fn l_List_isSuffixOf___redArg(
    mut v_inst_4945_: *mut leanh::LeanObject,
    mut v_l_u2081_4946_: *mut leanh::LeanObject,
    mut v_l_u2082_4947_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: u8 = 0;
    v___x_4948_ = l_List_reverse___redArg(v_l_u2081_4946_);
    v___x_4949_ = l_List_reverse___redArg(v_l_u2082_4947_);
    v___x_4950_ = l_List_isPrefixOf___redArg(v_inst_4945_, v___x_4948_, v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_List_isSuffixOf___redArg___boxed(
    mut v_inst_4951_: *mut leanh::LeanObject,
    mut v_l_u2081_4952_: *mut leanh::LeanObject,
    mut v_l_u2082_4953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4954_: u8 = 0;
    let mut v_r_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4954_ = l_List_isSuffixOf___redArg(v_inst_4951_, v_l_u2081_4952_, v_l_u2082_4953_);
    v_r_4955_ = leanh::lean_box((v_res_4954_) as usize);
    return v_r_4955_;
}
pub unsafe fn l_List_isSuffixOf(
    mut v_00_u03b1_4956_: *mut leanh::LeanObject,
    mut v_inst_4957_: *mut leanh::LeanObject,
    mut v_l_u2081_4958_: *mut leanh::LeanObject,
    mut v_l_u2082_4959_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4960_: u8 = 0;
    v___x_4960_ = l_List_isSuffixOf___redArg(v_inst_4957_, v_l_u2081_4958_, v_l_u2082_4959_);
    return v___x_4960_;
}
pub unsafe fn l_List_isSuffixOf___boxed(
    mut v_00_u03b1_4961_: *mut leanh::LeanObject,
    mut v_inst_4962_: *mut leanh::LeanObject,
    mut v_l_u2081_4963_: *mut leanh::LeanObject,
    mut v_l_u2082_4964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4965_: u8 = 0;
    let mut v_r_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4965_ = l_List_isSuffixOf(
        v_00_u03b1_4961_,
        v_inst_4962_,
        v_l_u2081_4963_,
        v_l_u2082_4964_,
    );
    v_r_4966_ = leanh::lean_box((v_res_4965_) as usize);
    return v_r_4966_;
}
pub unsafe fn l_List_isSuffixOf_x3f___redArg(
    mut v_inst_4967_: *mut leanh::LeanObject,
    mut v_l_u2081_4968_: *mut leanh::LeanObject,
    mut v_l_u2082_4969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4970_ = l_List_reverse___redArg(v_l_u2081_4968_);
                v___x_4971_ = l_List_reverse___redArg(v_l_u2082_4969_);
                v___x_4972_ =
                    l_List_isPrefixOf_x3f___redArg(v_inst_4967_, v___x_4970_, v___x_4971_);
                if leanh::lean_obj_tag(v___x_4972_) == 0 {
                    return v___x_4972_;
                } else {
                    v_val_4973_ = leanh::lean_ctor_get(v___x_4972_, 0);
                    v_isSharedCheck_4981_ = (!leanh::lean_is_exclusive(v___x_4972_)) as u8;
                    if v_isSharedCheck_4981_ == 0 {
                        v___x_4975_ = v___x_4972_;
                        v_isShared_4976_ = v_isSharedCheck_4981_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4973_);
                        leanh::lean_dec(v___x_4972_);
                        v___x_4975_ = leanh::lean_box(0);
                        v_isShared_4976_ = v_isSharedCheck_4981_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4977_ = l_List_reverse___redArg(v_val_4973_);
                if v_isShared_4976_ == 0 {
                    leanh::lean_ctor_set(v___x_4975_, 0, v___x_4977_);
                    v___x_4979_ = v___x_4975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4977_);
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
    mut v_00_u03b1_4982_: *mut leanh::LeanObject,
    mut v_inst_4983_: *mut leanh::LeanObject,
    mut v_l_u2081_4984_: *mut leanh::LeanObject,
    mut v_l_u2082_4985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l_List_isSuffixOf_x3f___redArg(v_inst_4983_, v_l_u2081_4984_, v_l_u2082_4985_);
    return v___x_4986_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5004_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__0;
    v___x_5005_ = l_String_toRawSubstring_x27(v___x_5004_);
    return v___x_5005_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(
    mut v_x_5017_: *mut leanh::LeanObject,
    mut v_a_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u8 = 0;
    v___x_5020_ = l_List_term___x3c_x3a_x2b___00__closed__1;
    leanh::lean_inc(v_x_5017_);
    v___x_5021_ = l_Lean_Syntax_isOfKind(v_x_5017_, v___x_5020_);
    if v___x_5021_ == 0 {
        let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5017_);
        v___x_5022_ = leanh::lean_box(1);
        v___x_5023_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5023_, 0, v___x_5022_);
        leanh::lean_ctor_set(v___x_5023_, 1, v_a_5019_);
        return v___x_5023_;
    } else {
        let mut v_quotContext_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5031_: u8 = 0;
        let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5024_ = leanh::lean_ctor_get(v_a_5018_, 1);
        v_currMacroScope_5025_ = leanh::lean_ctor_get(v_a_5018_, 2);
        v_ref_5026_ = leanh::lean_ctor_get(v_a_5018_, 5);
        v___x_5027_ = leanh::lean_unsigned_to_nat(0);
        v___x_5028_ = l_Lean_Syntax_getArg(v_x_5017_, v___x_5027_);
        v___x_5029_ = leanh::lean_unsigned_to_nat(2);
        v___x_5030_ = l_Lean_Syntax_getArg(v_x_5017_, v___x_5029_);
        leanh::lean_dec(v_x_5017_);
        v___x_5031_ = 0;
        v___x_5032_ = l_Lean_SourceInfo_fromRef(v_ref_5026_, v___x_5031_);
        v___x_5033_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5034_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__1);
        v___x_5035_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__2;
        leanh::lean_inc(v_currMacroScope_5025_);
        leanh::lean_inc(v_quotContext_5024_);
        v___x_5036_ =
            l_Lean_addMacroScope(v_quotContext_5024_, v___x_5035_, v_currMacroScope_5025_);
        v___x_5037_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___closed__5;
        leanh::lean_inc_n(v___x_5032_, 2);
        v___x_5038_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_5038_, 0, v___x_5032_);
        leanh::lean_ctor_set(v___x_5038_, 1, v___x_5034_);
        leanh::lean_ctor_set(v___x_5038_, 2, v___x_5036_);
        leanh::lean_ctor_set(v___x_5038_, 3, v___x_5037_);
        v___x_5039_ = l_List_lex___auto__1___closed__9;
        v___x_5040_ = l_Lean_Syntax_node2(v___x_5032_, v___x_5039_, v___x_5028_, v___x_5030_);
        v___x_5041_ = l_Lean_Syntax_node2(v___x_5032_, v___x_5033_, v___x_5038_, v___x_5040_);
        v___x_5042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5042_, 0, v___x_5041_);
        leanh::lean_ctor_set(v___x_5042_, 1, v_a_5019_);
        return v___x_5042_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1___boxed(
    mut v_x_5043_: *mut leanh::LeanObject,
    mut v_a_5044_: *mut leanh::LeanObject,
    mut v_a_5045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5046_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b____1(
            v_x_5043_, v_a_5044_, v_a_5045_,
        );
    leanh::lean_dec_ref(v_a_5044_);
    return v_res_5046_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(
    mut v_x_5047_: *mut leanh::LeanObject,
    mut v_a_5048_: *mut leanh::LeanObject,
    mut v_a_5049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    v___x_5050_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    leanh::lean_inc(v_x_5047_);
    v___x_5051_ = l_Lean_Syntax_isOfKind(v_x_5047_, v___x_5050_);
    if v___x_5051_ == 0 {
        let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5047_);
        v___x_5052_ = leanh::lean_box(0);
        v___x_5053_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5053_, 0, v___x_5052_);
        leanh::lean_ctor_set(v___x_5053_, 1, v_a_5049_);
        return v___x_5053_;
    } else {
        let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5057_: u8 = 0;
        v___x_5054_ = leanh::lean_unsigned_to_nat(0);
        v___x_5055_ = l_Lean_Syntax_getArg(v_x_5047_, v___x_5054_);
        v___x_5056_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        leanh::lean_inc(v___x_5055_);
        v___x_5057_ = l_Lean_Syntax_isOfKind(v___x_5055_, v___x_5056_);
        if v___x_5057_ == 0 {
            let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_5055_);
            leanh::lean_dec(v_x_5047_);
            v___x_5058_ = leanh::lean_box(0);
            v___x_5059_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5059_, 0, v___x_5058_);
            leanh::lean_ctor_set(v___x_5059_, 1, v_a_5049_);
            return v___x_5059_;
        } else {
            let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5063_: u8 = 0;
            v___x_5060_ = leanh::lean_unsigned_to_nat(1);
            v___x_5061_ = l_Lean_Syntax_getArg(v_x_5047_, v___x_5060_);
            leanh::lean_dec(v_x_5047_);
            v___x_5062_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_5061_);
            v___x_5063_ = l_Lean_Syntax_matchesNull(v___x_5061_, v___x_5062_);
            if v___x_5063_ == 0 {
                let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_5061_);
                leanh::lean_dec(v___x_5055_);
                v___x_5064_ = leanh::lean_box(0);
                v___x_5065_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5065_, 0, v___x_5064_);
                leanh::lean_ctor_set(v___x_5065_, 1, v_a_5049_);
                return v___x_5065_;
            } else {
                let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5069_: u8 = 0;
                let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5066_ = l_Lean_Syntax_getArg(v___x_5061_, v___x_5054_);
                v___x_5067_ = l_Lean_Syntax_getArg(v___x_5061_, v___x_5060_);
                leanh::lean_dec(v___x_5061_);
                v_ref_5068_ = l_Lean_replaceRef(v___x_5055_, v_a_5048_);
                leanh::lean_dec(v___x_5055_);
                v___x_5069_ = 0;
                v___x_5070_ = l_Lean_SourceInfo_fromRef(v_ref_5068_, v___x_5069_);
                leanh::lean_dec(v_ref_5068_);
                v___x_5071_ = l_List_term___x3c_x3a_x2b___00__closed__1;
                v___x_5072_ = l_List_term___x3c_x3a_x2b___00__closed__2;
                leanh::lean_inc(v___x_5070_);
                v___x_5073_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5073_, 0, v___x_5070_);
                leanh::lean_ctor_set(v___x_5073_, 1, v___x_5072_);
                v___x_5074_ = l_Lean_Syntax_node3(
                    v___x_5070_,
                    v___x_5071_,
                    v___x_5066_,
                    v___x_5073_,
                    v___x_5067_,
                );
                v___x_5075_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5075_, 0, v___x_5074_);
                leanh::lean_ctor_set(v___x_5075_, 1, v_a_5049_);
                return v___x_5075_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1___boxed(
    mut v_x_5076_: *mut leanh::LeanObject,
    mut v_a_5077_: *mut leanh::LeanObject,
    mut v_a_5078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsSuffix__1(
        v_x_5076_, v_a_5077_, v_a_5078_,
    );
    leanh::lean_dec(v_a_5077_);
    return v_res_5079_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5097_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__0;
    v___x_5098_ = l_String_toRawSubstring_x27(v___x_5097_);
    return v___x_5098_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(
    mut v_x_5110_: *mut leanh::LeanObject,
    mut v_a_5111_: *mut leanh::LeanObject,
    mut v_a_5112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    v___x_5113_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__1;
    leanh::lean_inc(v_x_5110_);
    v___x_5114_ = l_Lean_Syntax_isOfKind(v_x_5110_, v___x_5113_);
    if v___x_5114_ == 0 {
        let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5110_);
        v___x_5115_ = leanh::lean_box(1);
        v___x_5116_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5116_, 0, v___x_5115_);
        leanh::lean_ctor_set(v___x_5116_, 1, v_a_5112_);
        return v___x_5116_;
    } else {
        let mut v_quotContext_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5124_: u8 = 0;
        let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5117_ = leanh::lean_ctor_get(v_a_5111_, 1);
        v_currMacroScope_5118_ = leanh::lean_ctor_get(v_a_5111_, 2);
        v_ref_5119_ = leanh::lean_ctor_get(v_a_5111_, 5);
        v___x_5120_ = leanh::lean_unsigned_to_nat(0);
        v___x_5121_ = l_Lean_Syntax_getArg(v_x_5110_, v___x_5120_);
        v___x_5122_ = leanh::lean_unsigned_to_nat(2);
        v___x_5123_ = l_Lean_Syntax_getArg(v_x_5110_, v___x_5122_);
        leanh::lean_dec(v_x_5110_);
        v___x_5124_ = 0;
        v___x_5125_ = l_Lean_SourceInfo_fromRef(v_ref_5119_, v___x_5124_);
        v___x_5126_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__1);
        v___x_5128_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__2;
        leanh::lean_inc(v_currMacroScope_5118_);
        leanh::lean_inc(v_quotContext_5117_);
        v___x_5129_ =
            l_Lean_addMacroScope(v_quotContext_5117_, v___x_5128_, v_currMacroScope_5118_);
        v___x_5130_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___closed__5;
        leanh::lean_inc_n(v___x_5125_, 2);
        v___x_5131_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_5131_, 0, v___x_5125_);
        leanh::lean_ctor_set(v___x_5131_, 1, v___x_5127_);
        leanh::lean_ctor_set(v___x_5131_, 2, v___x_5129_);
        leanh::lean_ctor_set(v___x_5131_, 3, v___x_5130_);
        v___x_5132_ = l_List_lex___auto__1___closed__9;
        v___x_5133_ = l_Lean_Syntax_node2(v___x_5125_, v___x_5132_, v___x_5121_, v___x_5123_);
        v___x_5134_ = l_Lean_Syntax_node2(v___x_5125_, v___x_5126_, v___x_5131_, v___x_5133_);
        v___x_5135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5135_, 0, v___x_5134_);
        leanh::lean_ctor_set(v___x_5135_, 1, v_a_5112_);
        return v___x_5135_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1___boxed(
    mut v_x_5136_: *mut leanh::LeanObject,
    mut v_a_5137_: *mut leanh::LeanObject,
    mut v_a_5138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5139_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x3a_x2b_x3a____1(
            v_x_5136_, v_a_5137_, v_a_5138_,
        );
    leanh::lean_dec_ref(v_a_5137_);
    return v_res_5139_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(
    mut v_x_5140_: *mut leanh::LeanObject,
    mut v_a_5141_: *mut leanh::LeanObject,
    mut v_a_5142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: u8 = 0;
    v___x_5143_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    leanh::lean_inc(v_x_5140_);
    v___x_5144_ = l_Lean_Syntax_isOfKind(v_x_5140_, v___x_5143_);
    if v___x_5144_ == 0 {
        let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5140_);
        v___x_5145_ = leanh::lean_box(0);
        v___x_5146_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
        leanh::lean_ctor_set(v___x_5146_, 1, v_a_5142_);
        return v___x_5146_;
    } else {
        let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5150_: u8 = 0;
        v___x_5147_ = leanh::lean_unsigned_to_nat(0);
        v___x_5148_ = l_Lean_Syntax_getArg(v_x_5140_, v___x_5147_);
        v___x_5149_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        leanh::lean_inc(v___x_5148_);
        v___x_5150_ = l_Lean_Syntax_isOfKind(v___x_5148_, v___x_5149_);
        if v___x_5150_ == 0 {
            let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_5148_);
            leanh::lean_dec(v_x_5140_);
            v___x_5151_ = leanh::lean_box(0);
            v___x_5152_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
            leanh::lean_ctor_set(v___x_5152_, 1, v_a_5142_);
            return v___x_5152_;
        } else {
            let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5156_: u8 = 0;
            v___x_5153_ = leanh::lean_unsigned_to_nat(1);
            v___x_5154_ = l_Lean_Syntax_getArg(v_x_5140_, v___x_5153_);
            leanh::lean_dec(v_x_5140_);
            v___x_5155_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_5154_);
            v___x_5156_ = l_Lean_Syntax_matchesNull(v___x_5154_, v___x_5155_);
            if v___x_5156_ == 0 {
                let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_5154_);
                leanh::lean_dec(v___x_5148_);
                v___x_5157_ = leanh::lean_box(0);
                v___x_5158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5158_, 0, v___x_5157_);
                leanh::lean_ctor_set(v___x_5158_, 1, v_a_5142_);
                return v___x_5158_;
            } else {
                let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5162_: u8 = 0;
                let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5159_ = l_Lean_Syntax_getArg(v___x_5154_, v___x_5147_);
                v___x_5160_ = l_Lean_Syntax_getArg(v___x_5154_, v___x_5153_);
                leanh::lean_dec(v___x_5154_);
                v_ref_5161_ = l_Lean_replaceRef(v___x_5148_, v_a_5141_);
                leanh::lean_dec(v___x_5148_);
                v___x_5162_ = 0;
                v___x_5163_ = l_Lean_SourceInfo_fromRef(v_ref_5161_, v___x_5162_);
                leanh::lean_dec(v_ref_5161_);
                v___x_5164_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__1;
                v___x_5165_ = l_List_term___x3c_x3a_x2b_x3a___00__closed__2;
                leanh::lean_inc(v___x_5163_);
                v___x_5166_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5166_, 0, v___x_5163_);
                leanh::lean_ctor_set(v___x_5166_, 1, v___x_5165_);
                v___x_5167_ = l_Lean_Syntax_node3(
                    v___x_5163_,
                    v___x_5164_,
                    v___x_5159_,
                    v___x_5166_,
                    v___x_5160_,
                );
                v___x_5168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5168_, 0, v___x_5167_);
                leanh::lean_ctor_set(v___x_5168_, 1, v_a_5142_);
                return v___x_5168_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1___boxed(
    mut v_x_5169_: *mut leanh::LeanObject,
    mut v_a_5170_: *mut leanh::LeanObject,
    mut v_a_5171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5172_ = l_List___aux__Init__Data__List__Basic______unexpand__List__IsInfix__1(
        v_x_5169_, v_a_5170_, v_a_5171_,
    );
    leanh::lean_dec(v_a_5170_);
    return v_res_5172_;
}
pub unsafe fn l_List_isInfixOf__internal___redArg(
    mut v_inst_5173_: *mut leanh::LeanObject,
    mut v_l_u2081_5174_: *mut leanh::LeanObject,
    mut v_l_u2082_5175_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5176_: u8 = 0;
    let mut v_tail_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_l_u2082_5175_);
                leanh::lean_inc(v_l_u2081_5174_);
                leanh::lean_inc_ref(v_inst_5173_);
                v___x_5176_ =
                    l_List_isPrefixOf___redArg(v_inst_5173_, v_l_u2081_5174_, v_l_u2082_5175_);
                if v___x_5176_ == 0 {
                    if leanh::lean_obj_tag(v_l_u2082_5175_) == 0 {
                        leanh::lean_dec(v_l_u2081_5174_);
                        leanh::lean_dec_ref(v_inst_5173_);
                        return v___x_5176_;
                    } else {
                        v_tail_5177_ = leanh::lean_ctor_get(v_l_u2082_5175_, 1);
                        leanh::lean_inc(v_tail_5177_);
                        leanh::lean_dec_ref_known(v_l_u2082_5175_, 2);
                        v_l_u2082_5175_ = v_tail_5177_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_l_u2082_5175_);
                    leanh::lean_dec(v_l_u2081_5174_);
                    leanh::lean_dec_ref(v_inst_5173_);
                    return v___x_5176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isInfixOf__internal___redArg___boxed(
    mut v_inst_5179_: *mut leanh::LeanObject,
    mut v_l_u2081_5180_: *mut leanh::LeanObject,
    mut v_l_u2082_5181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5182_: u8 = 0;
    let mut v_r_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5182_ =
        l_List_isInfixOf__internal___redArg(v_inst_5179_, v_l_u2081_5180_, v_l_u2082_5181_);
    v_r_5183_ = leanh::lean_box((v_res_5182_) as usize);
    return v_r_5183_;
}
pub unsafe fn l_List_isInfixOf__internal(
    mut v_00_u03b1_5184_: *mut leanh::LeanObject,
    mut v_inst_5185_: *mut leanh::LeanObject,
    mut v_l_u2081_5186_: *mut leanh::LeanObject,
    mut v_l_u2082_5187_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5188_: u8 = 0;
    v___x_5188_ =
        l_List_isInfixOf__internal___redArg(v_inst_5185_, v_l_u2081_5186_, v_l_u2082_5187_);
    return v___x_5188_;
}
pub unsafe fn l_List_isInfixOf__internal___boxed(
    mut v_00_u03b1_5189_: *mut leanh::LeanObject,
    mut v_inst_5190_: *mut leanh::LeanObject,
    mut v_l_u2081_5191_: *mut leanh::LeanObject,
    mut v_l_u2082_5192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5193_: u8 = 0;
    let mut v_r_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_List_isInfixOf__internal(
        v_00_u03b1_5189_,
        v_inst_5190_,
        v_l_u2081_5191_,
        v_l_u2082_5192_,
    );
    v_r_5194_ = leanh::lean_box((v_res_5193_) as usize);
    return v_r_5194_;
}
pub unsafe fn l_List_splitAt_go___redArg(
    mut v_l_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
    mut v_a_5197_: *mut leanh::LeanObject,
    mut v_a_5198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5203_: u8 = 0;
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5208_: u8 = 0;
    let mut v_one_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_unused_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5196_) == 0 {
                    leanh::lean_dec(v_a_5198_);
                    leanh::lean_dec(v_a_5197_);
                    v___x_5199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5199_, 0, v_l_5195_);
                    leanh::lean_ctor_set(v___x_5199_, 1, v_a_5196_);
                    return v___x_5199_;
                } else {
                    v_head_5200_ = leanh::lean_ctor_get(v_a_5196_, 0);
                    v_tail_5201_ = leanh::lean_ctor_get(v_a_5196_, 1);
                    v_zero_5202_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_5203_ = lean_nat_dec_eq(v_a_5197_, v_zero_5202_);
                    if v_isZero_5203_ == 1 {
                        leanh::lean_dec(v_a_5197_);
                        leanh::lean_dec(v_l_5195_);
                        v___x_5204_ = l_List_reverse___redArg(v_a_5198_);
                        v___x_5205_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5205_, 0, v___x_5204_);
                        leanh::lean_ctor_set(v___x_5205_, 1, v_a_5196_);
                        return v___x_5205_;
                    } else {
                        leanh::lean_inc(v_tail_5201_);
                        leanh::lean_inc(v_head_5200_);
                        v_isSharedCheck_5215_ = (!leanh::lean_is_exclusive(v_a_5196_)) as u8;
                        if v_isSharedCheck_5215_ == 0 {
                            v_unused_5216_ = leanh::lean_ctor_get(v_a_5196_, 1);
                            leanh::lean_dec(v_unused_5216_);
                            v_unused_5217_ = leanh::lean_ctor_get(v_a_5196_, 0);
                            leanh::lean_dec(v_unused_5217_);
                            v___x_5207_ = v_a_5196_;
                            v_isShared_5208_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_5196_);
                            v___x_5207_ = leanh::lean_box(0);
                            v_isShared_5208_ = v_isSharedCheck_5215_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5209_ = leanh::lean_unsigned_to_nat(1);
                v_n_5210_ = lean_nat_sub(v_a_5197_, v_one_5209_);
                leanh::lean_dec(v_a_5197_);
                if v_isShared_5208_ == 0 {
                    leanh::lean_ctor_set(v___x_5207_, 1, v_a_5198_);
                    v___x_5212_ = v___x_5207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_head_5200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 1, v_a_5198_);
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
    mut v_00_u03b1_5218_: *mut leanh::LeanObject,
    mut v_l_5219_: *mut leanh::LeanObject,
    mut v_a_5220_: *mut leanh::LeanObject,
    mut v_a_5221_: *mut leanh::LeanObject,
    mut v_a_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = l_List_splitAt_go___redArg(v_l_5219_, v_a_5220_, v_a_5221_, v_a_5222_);
    return v___x_5223_;
}
pub unsafe fn l_List_splitAt___redArg(
    mut v_n_5224_: *mut leanh::LeanObject,
    mut v_l_5225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = leanh::lean_box(0);
    leanh::lean_inc(v_l_5225_);
    v___x_5227_ = l_List_splitAt_go___redArg(v_l_5225_, v_l_5225_, v_n_5224_, v___x_5226_);
    return v___x_5227_;
}
pub unsafe fn l_List_splitAt(
    mut v_00_u03b1_5228_: *mut leanh::LeanObject,
    mut v_n_5229_: *mut leanh::LeanObject,
    mut v_l_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5231_ = l_List_splitAt___redArg(v_n_5229_, v_l_5230_);
    return v___x_5231_;
}
pub unsafe fn l_List_rotateLeft___redArg(
    mut v_xs_5232_: *mut leanh::LeanObject,
    mut v_i_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_len_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    v_len_5234_ = l_List_length___redArg(v_xs_5232_);
    v___x_5235_ = leanh::lean_unsigned_to_nat(1);
    v___x_5236_ = lean_nat_dec_le(v_len_5234_, v___x_5235_);
    if v___x_5236_ == 0 {
        let mut v_i_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ys_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zs_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_5237_ = lean_nat_mod(v_i_5233_, v_len_5234_);
        leanh::lean_dec(v_len_5234_);
        leanh::lean_inc(v_xs_5232_);
        v_ys_5238_ = l_List_take___redArg(v_i_5237_, v_xs_5232_);
        v_zs_5239_ = l_List_drop___redArg(v_i_5237_, v_xs_5232_);
        leanh::lean_dec(v_xs_5232_);
        v___x_5240_ = l_List_appendTR___redArg(v_zs_5239_, v_ys_5238_);
        return v___x_5240_;
    } else {
        leanh::lean_dec(v_len_5234_);
        return v_xs_5232_;
    }
}
pub unsafe fn l_List_rotateLeft___redArg___boxed(
    mut v_xs_5241_: *mut leanh::LeanObject,
    mut v_i_5242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5243_ = l_List_rotateLeft___redArg(v_xs_5241_, v_i_5242_);
    leanh::lean_dec(v_i_5242_);
    return v_res_5243_;
}
pub unsafe fn l_List_rotateLeft(
    mut v_00_u03b1_5244_: *mut leanh::LeanObject,
    mut v_xs_5245_: *mut leanh::LeanObject,
    mut v_i_5246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5247_ = l_List_rotateLeft___redArg(v_xs_5245_, v_i_5246_);
    return v___x_5247_;
}
pub unsafe fn l_List_rotateLeft___boxed(
    mut v_00_u03b1_5248_: *mut leanh::LeanObject,
    mut v_xs_5249_: *mut leanh::LeanObject,
    mut v_i_5250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5251_ = l_List_rotateLeft(v_00_u03b1_5248_, v_xs_5249_, v_i_5250_);
    leanh::lean_dec(v_i_5250_);
    return v_res_5251_;
}
pub unsafe fn l_List_rotateRight___redArg(
    mut v_xs_5252_: *mut leanh::LeanObject,
    mut v_i_5253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_len_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: u8 = 0;
    v_len_5254_ = l_List_length___redArg(v_xs_5252_);
    v___x_5255_ = leanh::lean_unsigned_to_nat(1);
    v___x_5256_ = lean_nat_dec_le(v_len_5254_, v___x_5255_);
    if v___x_5256_ == 0 {
        let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_i_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ys_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_zs_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5257_ = lean_nat_mod(v_i_5253_, v_len_5254_);
        v_i_5258_ = lean_nat_sub(v_len_5254_, v___x_5257_);
        leanh::lean_dec(v___x_5257_);
        leanh::lean_dec(v_len_5254_);
        leanh::lean_inc(v_xs_5252_);
        v_ys_5259_ = l_List_take___redArg(v_i_5258_, v_xs_5252_);
        v_zs_5260_ = l_List_drop___redArg(v_i_5258_, v_xs_5252_);
        leanh::lean_dec(v_xs_5252_);
        v___x_5261_ = l_List_appendTR___redArg(v_zs_5260_, v_ys_5259_);
        return v___x_5261_;
    } else {
        leanh::lean_dec(v_len_5254_);
        return v_xs_5252_;
    }
}
pub unsafe fn l_List_rotateRight___redArg___boxed(
    mut v_xs_5262_: *mut leanh::LeanObject,
    mut v_i_5263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5264_ = l_List_rotateRight___redArg(v_xs_5262_, v_i_5263_);
    leanh::lean_dec(v_i_5263_);
    return v_res_5264_;
}
pub unsafe fn l_List_rotateRight(
    mut v_00_u03b1_5265_: *mut leanh::LeanObject,
    mut v_xs_5266_: *mut leanh::LeanObject,
    mut v_i_5267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5268_ = l_List_rotateRight___redArg(v_xs_5266_, v_i_5267_);
    return v___x_5268_;
}
pub unsafe fn l_List_rotateRight___boxed(
    mut v_00_u03b1_5269_: *mut leanh::LeanObject,
    mut v_xs_5270_: *mut leanh::LeanObject,
    mut v_i_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l_List_rotateRight(v_00_u03b1_5269_, v_xs_5270_, v_i_5271_);
    leanh::lean_dec(v_i_5271_);
    return v_res_5272_;
}
pub unsafe fn l_List_instDecidablePairwise___redArg(
    mut v_inst_5273_: *mut leanh::LeanObject,
    mut v_x_5274_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5274_) == 0 {
        let mut v___x_5275_: u8 = 0;
        leanh::lean_dec_ref(v_inst_5273_);
        v___x_5275_ = 1;
        return v___x_5275_;
    } else {
        let mut v_head_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5278_: u8 = 0;
        v_head_5276_ = leanh::lean_ctor_get(v_x_5274_, 0);
        leanh::lean_inc(v_head_5276_);
        v_tail_5277_ = leanh::lean_ctor_get(v_x_5274_, 1);
        leanh::lean_inc_n(v_tail_5277_, 2);
        leanh::lean_dec_ref_known(v_x_5274_, 2);
        leanh::lean_inc_ref(v_inst_5273_);
        v___x_5278_ = l_List_instDecidablePairwise___redArg(v_inst_5273_, v_tail_5277_);
        if v___x_5278_ == 0 {
            leanh::lean_dec(v_tail_5277_);
            leanh::lean_dec(v_head_5276_);
            leanh::lean_dec_ref(v_inst_5273_);
            return v___x_5278_;
        } else {
            let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5280_: u8 = 0;
            v___x_5279_ = leanh::lean_apply_1(v_inst_5273_, v_head_5276_);
            v___x_5280_ = l_List_decidableBAll___redArg(v___x_5279_, v_tail_5277_);
            return v___x_5280_;
        }
    }
}
pub unsafe fn l_List_instDecidablePairwise___redArg___boxed(
    mut v_inst_5281_: *mut leanh::LeanObject,
    mut v_x_5282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5283_: u8 = 0;
    let mut v_r_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_List_instDecidablePairwise___redArg(v_inst_5281_, v_x_5282_);
    v_r_5284_ = leanh::lean_box((v_res_5283_) as usize);
    return v_r_5284_;
}
pub unsafe fn l_List_instDecidablePairwise(
    mut v_00_u03b1_5285_: *mut leanh::LeanObject,
    mut v_R_5286_: *mut leanh::LeanObject,
    mut v_inst_5287_: *mut leanh::LeanObject,
    mut v_x_5288_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5289_: u8 = 0;
    v___x_5289_ = l_List_instDecidablePairwise___redArg(v_inst_5287_, v_x_5288_);
    return v___x_5289_;
}
pub unsafe fn l_List_instDecidablePairwise___boxed(
    mut v_00_u03b1_5290_: *mut leanh::LeanObject,
    mut v_R_5291_: *mut leanh::LeanObject,
    mut v_inst_5292_: *mut leanh::LeanObject,
    mut v_x_5293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5294_: u8 = 0;
    let mut v_r_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ =
        l_List_instDecidablePairwise(v_00_u03b1_5290_, v_R_5291_, v_inst_5292_, v_x_5293_);
    v_r_5295_ = leanh::lean_box((v_res_5294_) as usize);
    return v_r_5295_;
}
pub unsafe fn l_List_nodupDecidable___redArg___lam__0(
    mut v_inst_5296_: *mut leanh::LeanObject,
    mut v_a_5297_: *mut leanh::LeanObject,
    mut v_b_5298_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: u8 = 0;
    v___x_5299_ = leanh::lean_apply_2(v_inst_5296_, v_a_5297_, v_b_5298_);
    v___x_5300_ = (leanh::lean_unbox(v___x_5299_) as u8);
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
    mut v_inst_5303_: *mut leanh::LeanObject,
    mut v_a_5304_: *mut leanh::LeanObject,
    mut v_b_5305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5306_: u8 = 0;
    let mut v_r_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l_List_nodupDecidable___redArg___lam__0(v_inst_5303_, v_a_5304_, v_b_5305_);
    v_r_5307_ = leanh::lean_box((v_res_5306_) as usize);
    return v_r_5307_;
}
pub unsafe fn l_List_nodupDecidable___redArg(
    mut v_inst_5308_: *mut leanh::LeanObject,
    mut v_l_5309_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: u8 = 0;
    v___f_5310_ = leanh::lean_alloc_closure(
        l_List_nodupDecidable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5310_, 0, v_inst_5308_);
    v___x_5311_ = l_List_instDecidablePairwise___redArg(v___f_5310_, v_l_5309_);
    return v___x_5311_;
}
pub unsafe fn l_List_nodupDecidable___redArg___boxed(
    mut v_inst_5312_: *mut leanh::LeanObject,
    mut v_l_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5314_: u8 = 0;
    let mut v_r_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_List_nodupDecidable___redArg(v_inst_5312_, v_l_5313_);
    v_r_5315_ = leanh::lean_box((v_res_5314_) as usize);
    return v_r_5315_;
}
pub unsafe fn l_List_nodupDecidable(
    mut v_00_u03b1_5316_: *mut leanh::LeanObject,
    mut v_inst_5317_: *mut leanh::LeanObject,
    mut v_l_5318_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5319_: u8 = 0;
    v___x_5319_ = l_List_nodupDecidable___redArg(v_inst_5317_, v_l_5318_);
    return v___x_5319_;
}
pub unsafe fn l_List_nodupDecidable___boxed(
    mut v_00_u03b1_5320_: *mut leanh::LeanObject,
    mut v_inst_5321_: *mut leanh::LeanObject,
    mut v_l_5322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5323_: u8 = 0;
    let mut v_r_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5323_ = l_List_nodupDecidable(v_00_u03b1_5320_, v_inst_5321_, v_l_5322_);
    v_r_5324_ = leanh::lean_box((v_res_5323_) as usize);
    return v_r_5324_;
}
pub unsafe fn l_List_replace___redArg(
    mut v_inst_5325_: *mut leanh::LeanObject,
    mut v_x_5326_: *mut leanh::LeanObject,
    mut v_x_5327_: *mut leanh::LeanObject,
    mut v_x_5328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5326_) == 0 {
                    leanh::lean_dec(v_x_5328_);
                    leanh::lean_dec(v_x_5327_);
                    leanh::lean_dec_ref(v_inst_5325_);
                    return v_x_5326_;
                } else {
                    v_head_5329_ = leanh::lean_ctor_get(v_x_5326_, 0);
                    v_tail_5330_ = leanh::lean_ctor_get(v_x_5326_, 1);
                    v_isSharedCheck_5343_ = (!leanh::lean_is_exclusive(v_x_5326_)) as u8;
                    if v_isSharedCheck_5343_ == 0 {
                        v___x_5332_ = v_x_5326_;
                        v_isShared_5333_ = v_isSharedCheck_5343_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5330_);
                        leanh::lean_inc(v_head_5329_);
                        leanh::lean_dec(v_x_5326_);
                        v___x_5332_ = leanh::lean_box(0);
                        v_isShared_5333_ = v_isSharedCheck_5343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_5325_);
                leanh::lean_inc(v_head_5329_);
                leanh::lean_inc(v_x_5327_);
                v___x_5334_ = leanh::lean_apply_2(v_inst_5325_, v_x_5327_, v_head_5329_);
                v___x_5335_ = (leanh::lean_unbox(v___x_5334_) as u8);
                if v___x_5335_ == 0 {
                    v___x_5336_ =
                        l_List_replace___redArg(v_inst_5325_, v_tail_5330_, v_x_5327_, v_x_5328_);
                    if v_isShared_5333_ == 0 {
                        leanh::lean_ctor_set(v___x_5332_, 1, v___x_5336_);
                        v___x_5338_ = v___x_5332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5339_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_head_5329_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5336_);
                        v___x_5338_ = v_reuseFailAlloc_5339_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_head_5329_);
                    leanh::lean_dec(v_x_5327_);
                    leanh::lean_dec_ref(v_inst_5325_);
                    if v_isShared_5333_ == 0 {
                        leanh::lean_ctor_set(v___x_5332_, 0, v_x_5328_);
                        v___x_5341_ = v___x_5332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5342_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_x_5328_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_tail_5330_);
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
    mut v_00_u03b1_5344_: *mut leanh::LeanObject,
    mut v_inst_5345_: *mut leanh::LeanObject,
    mut v_x_5346_: *mut leanh::LeanObject,
    mut v_x_5347_: *mut leanh::LeanObject,
    mut v_x_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5349_ = l_List_replace___redArg(v_inst_5345_, v_x_5346_, v_x_5347_, v_x_5348_);
    return v___x_5349_;
}
pub unsafe fn l_List_modifyTailIdx_go___redArg(
    mut v_f_5350_: *mut leanh::LeanObject,
    mut v_a_5351_: *mut leanh::LeanObject,
    mut v_a_5352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5354_: u8 = 0;
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v_one_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5353_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5354_ = lean_nat_dec_eq(v_a_5351_, v_zero_5353_);
                if v_isZero_5354_ == 1 {
                    v___x_5355_ = leanh::lean_apply_1(v_f_5350_, v_a_5352_);
                    return v___x_5355_;
                } else {
                    if leanh::lean_obj_tag(v_a_5352_) == 0 {
                        leanh::lean_dec_ref(v_f_5350_);
                        return v_a_5352_;
                    } else {
                        v_head_5356_ = leanh::lean_ctor_get(v_a_5352_, 0);
                        v_tail_5357_ = leanh::lean_ctor_get(v_a_5352_, 1);
                        v_isSharedCheck_5367_ = (!leanh::lean_is_exclusive(v_a_5352_)) as u8;
                        if v_isSharedCheck_5367_ == 0 {
                            v___x_5359_ = v_a_5352_;
                            v_isShared_5360_ = v_isSharedCheck_5367_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_5357_);
                            leanh::lean_inc(v_head_5356_);
                            leanh::lean_dec(v_a_5352_);
                            v___x_5359_ = leanh::lean_box(0);
                            v_isShared_5360_ = v_isSharedCheck_5367_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5361_ = leanh::lean_unsigned_to_nat(1);
                v_n_5362_ = lean_nat_sub(v_a_5351_, v_one_5361_);
                v___x_5363_ = l_List_modifyTailIdx_go___redArg(v_f_5350_, v_n_5362_, v_tail_5357_);
                leanh::lean_dec(v_n_5362_);
                if v_isShared_5360_ == 0 {
                    leanh::lean_ctor_set(v___x_5359_, 1, v___x_5363_);
                    v___x_5365_ = v___x_5359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_head_5356_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___x_5363_);
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
    mut v_f_5368_: *mut leanh::LeanObject,
    mut v_a_5369_: *mut leanh::LeanObject,
    mut v_a_5370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_List_modifyTailIdx_go___redArg(v_f_5368_, v_a_5369_, v_a_5370_);
    leanh::lean_dec(v_a_5369_);
    return v_res_5371_;
}
pub unsafe fn l_List_modifyTailIdx_go(
    mut v_00_u03b1_5372_: *mut leanh::LeanObject,
    mut v_f_5373_: *mut leanh::LeanObject,
    mut v_a_5374_: *mut leanh::LeanObject,
    mut v_a_5375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5376_ = l_List_modifyTailIdx_go___redArg(v_f_5373_, v_a_5374_, v_a_5375_);
    return v___x_5376_;
}
pub unsafe fn l_List_modifyTailIdx_go___boxed(
    mut v_00_u03b1_5377_: *mut leanh::LeanObject,
    mut v_f_5378_: *mut leanh::LeanObject,
    mut v_a_5379_: *mut leanh::LeanObject,
    mut v_a_5380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l_List_modifyTailIdx_go(v_00_u03b1_5377_, v_f_5378_, v_a_5379_, v_a_5380_);
    leanh::lean_dec(v_a_5379_);
    return v_res_5381_;
}
pub unsafe fn l_List_modifyTailIdx___redArg(
    mut v_l_5382_: *mut leanh::LeanObject,
    mut v_i_5383_: *mut leanh::LeanObject,
    mut v_f_5384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_List_modifyTailIdx_go___redArg(v_f_5384_, v_i_5383_, v_l_5382_);
    return v___x_5385_;
}
pub unsafe fn l_List_modifyTailIdx___redArg___boxed(
    mut v_l_5386_: *mut leanh::LeanObject,
    mut v_i_5387_: *mut leanh::LeanObject,
    mut v_f_5388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5389_ = l_List_modifyTailIdx___redArg(v_l_5386_, v_i_5387_, v_f_5388_);
    leanh::lean_dec(v_i_5387_);
    return v_res_5389_;
}
pub unsafe fn l_List_modifyTailIdx(
    mut v_00_u03b1_5390_: *mut leanh::LeanObject,
    mut v_l_5391_: *mut leanh::LeanObject,
    mut v_i_5392_: *mut leanh::LeanObject,
    mut v_f_5393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_List_modifyTailIdx_go___redArg(v_f_5393_, v_i_5392_, v_l_5391_);
    return v___x_5394_;
}
pub unsafe fn l_List_modifyTailIdx___boxed(
    mut v_00_u03b1_5395_: *mut leanh::LeanObject,
    mut v_l_5396_: *mut leanh::LeanObject,
    mut v_i_5397_: *mut leanh::LeanObject,
    mut v_f_5398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5399_ = l_List_modifyTailIdx(v_00_u03b1_5395_, v_l_5396_, v_i_5397_, v_f_5398_);
    leanh::lean_dec(v_i_5397_);
    return v_res_5399_;
}
pub unsafe fn l_List_modifyHead___redArg(
    mut v_f_5400_: *mut leanh::LeanObject,
    mut v_x_5401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5401_) == 0 {
                    leanh::lean_dec(v_f_5400_);
                    return v_x_5401_;
                } else {
                    v_head_5402_ = leanh::lean_ctor_get(v_x_5401_, 0);
                    v_tail_5403_ = leanh::lean_ctor_get(v_x_5401_, 1);
                    v_isSharedCheck_5411_ = (!leanh::lean_is_exclusive(v_x_5401_)) as u8;
                    if v_isSharedCheck_5411_ == 0 {
                        v___x_5405_ = v_x_5401_;
                        v_isShared_5406_ = v_isSharedCheck_5411_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5403_);
                        leanh::lean_inc(v_head_5402_);
                        leanh::lean_dec(v_x_5401_);
                        v___x_5405_ = leanh::lean_box(0);
                        v_isShared_5406_ = v_isSharedCheck_5411_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5407_ = leanh::lean_apply_1(v_f_5400_, v_head_5402_);
                if v_isShared_5406_ == 0 {
                    leanh::lean_ctor_set(v___x_5405_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5410_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_tail_5403_);
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
    mut v_00_u03b1_5412_: *mut leanh::LeanObject,
    mut v_f_5413_: *mut leanh::LeanObject,
    mut v_x_5414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5414_) == 0 {
                    leanh::lean_dec(v_f_5413_);
                    return v_x_5414_;
                } else {
                    v_head_5415_ = leanh::lean_ctor_get(v_x_5414_, 0);
                    v_tail_5416_ = leanh::lean_ctor_get(v_x_5414_, 1);
                    v_isSharedCheck_5424_ = (!leanh::lean_is_exclusive(v_x_5414_)) as u8;
                    if v_isSharedCheck_5424_ == 0 {
                        v___x_5418_ = v_x_5414_;
                        v_isShared_5419_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5416_);
                        leanh::lean_inc(v_head_5415_);
                        leanh::lean_dec(v_x_5414_);
                        v___x_5418_ = leanh::lean_box(0);
                        v_isShared_5419_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5420_ = leanh::lean_apply_1(v_f_5413_, v_head_5415_);
                if v_isShared_5419_ == 0 {
                    leanh::lean_ctor_set(v___x_5418_, 0, v___x_5420_);
                    v___x_5422_ = v___x_5418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_tail_5416_);
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
    mut v_l_5425_: *mut leanh::LeanObject,
    mut v_i_5426_: *mut leanh::LeanObject,
    mut v_f_5427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5428_ =
        leanh::lean_alloc_closure(l_List_modifyHead as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_5428_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5428_, 1, v_f_5427_);
    v___x_5429_ = l_List_modifyTailIdx_go___redArg(v___x_5428_, v_i_5426_, v_l_5425_);
    return v___x_5429_;
}
pub unsafe fn l_List_modify___redArg___boxed(
    mut v_l_5430_: *mut leanh::LeanObject,
    mut v_i_5431_: *mut leanh::LeanObject,
    mut v_f_5432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5433_ = l_List_modify___redArg(v_l_5430_, v_i_5431_, v_f_5432_);
    leanh::lean_dec(v_i_5431_);
    return v_res_5433_;
}
pub unsafe fn l_List_modify(
    mut v_00_u03b1_5434_: *mut leanh::LeanObject,
    mut v_l_5435_: *mut leanh::LeanObject,
    mut v_i_5436_: *mut leanh::LeanObject,
    mut v_f_5437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ =
        leanh::lean_alloc_closure(l_List_modifyHead as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_5438_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5438_, 1, v_f_5437_);
    v___x_5439_ = l_List_modifyTailIdx_go___redArg(v___x_5438_, v_i_5436_, v_l_5435_);
    return v___x_5439_;
}
pub unsafe fn l_List_modify___boxed(
    mut v_00_u03b1_5440_: *mut leanh::LeanObject,
    mut v_l_5441_: *mut leanh::LeanObject,
    mut v_i_5442_: *mut leanh::LeanObject,
    mut v_f_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ = l_List_modify(v_00_u03b1_5440_, v_l_5441_, v_i_5442_, v_f_5443_);
    leanh::lean_dec(v_i_5442_);
    return v_res_5444_;
}
pub unsafe fn l_List_insert___redArg(
    mut v_inst_5445_: *mut leanh::LeanObject,
    mut v_a_5446_: *mut leanh::LeanObject,
    mut v_l_5447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5448_: u8 = 0;
    leanh::lean_inc(v_l_5447_);
    leanh::lean_inc(v_a_5446_);
    v___x_5448_ = l_List_elem___redArg(v_inst_5445_, v_a_5446_, v_l_5447_);
    if v___x_5448_ == 0 {
        let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5449_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5449_, 0, v_a_5446_);
        leanh::lean_ctor_set(v___x_5449_, 1, v_l_5447_);
        return v___x_5449_;
    } else {
        leanh::lean_dec(v_a_5446_);
        return v_l_5447_;
    }
}
pub unsafe fn l_List_insert(
    mut v_00_u03b1_5450_: *mut leanh::LeanObject,
    mut v_inst_5451_: *mut leanh::LeanObject,
    mut v_a_5452_: *mut leanh::LeanObject,
    mut v_l_5453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5454_: u8 = 0;
    leanh::lean_inc(v_l_5453_);
    leanh::lean_inc(v_a_5452_);
    v___x_5454_ = l_List_elem___redArg(v_inst_5451_, v_a_5452_, v_l_5453_);
    if v___x_5454_ == 0 {
        let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5455_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5455_, 0, v_a_5452_);
        leanh::lean_ctor_set(v___x_5455_, 1, v_l_5453_);
        return v___x_5455_;
    } else {
        leanh::lean_dec(v_a_5452_);
        return v_l_5453_;
    }
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
    mut v_a_5456_: *mut leanh::LeanObject,
    mut v_a_5457_: *mut leanh::LeanObject,
    mut v_a_5458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5460_: u8 = 0;
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v_one_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5459_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5460_ = lean_nat_dec_eq(v_a_5457_, v_zero_5459_);
                if v_isZero_5460_ == 1 {
                    v___x_5461_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5461_, 0, v_a_5456_);
                    leanh::lean_ctor_set(v___x_5461_, 1, v_a_5458_);
                    return v___x_5461_;
                } else {
                    if leanh::lean_obj_tag(v_a_5458_) == 0 {
                        leanh::lean_dec(v_a_5456_);
                        return v_a_5458_;
                    } else {
                        v_head_5462_ = leanh::lean_ctor_get(v_a_5458_, 0);
                        v_tail_5463_ = leanh::lean_ctor_get(v_a_5458_, 1);
                        v_isSharedCheck_5473_ = (!leanh::lean_is_exclusive(v_a_5458_)) as u8;
                        if v_isSharedCheck_5473_ == 0 {
                            v___x_5465_ = v_a_5458_;
                            v_isShared_5466_ = v_isSharedCheck_5473_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_5463_);
                            leanh::lean_inc(v_head_5462_);
                            leanh::lean_dec(v_a_5458_);
                            v___x_5465_ = leanh::lean_box(0);
                            v_isShared_5466_ = v_isSharedCheck_5473_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_one_5467_ = leanh::lean_unsigned_to_nat(1);
                v_n_5468_ = lean_nat_sub(v_a_5457_, v_one_5467_);
                v___x_5469_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
                    v_a_5456_,
                    v_n_5468_,
                    v_tail_5463_,
                );
                leanh::lean_dec(v_n_5468_);
                if v_isShared_5466_ == 0 {
                    leanh::lean_ctor_set(v___x_5465_, 1, v___x_5469_);
                    v___x_5471_ = v___x_5465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5472_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_head_5462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 1, v___x_5469_);
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
    mut v_a_5474_: *mut leanh::LeanObject,
    mut v_a_5475_: *mut leanh::LeanObject,
    mut v_a_5476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5474_, v_a_5475_, v_a_5476_,
    );
    leanh::lean_dec(v_a_5475_);
    return v_res_5477_;
}
pub unsafe fn l_List_insertIdx___redArg(
    mut v_xs_5478_: *mut leanh::LeanObject,
    mut v_i_5479_: *mut leanh::LeanObject,
    mut v_a_5480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5481_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5480_, v_i_5479_, v_xs_5478_,
    );
    return v___x_5481_;
}
pub unsafe fn l_List_insertIdx___redArg___boxed(
    mut v_xs_5482_: *mut leanh::LeanObject,
    mut v_i_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_List_insertIdx___redArg(v_xs_5482_, v_i_5483_, v_a_5484_);
    leanh::lean_dec(v_i_5483_);
    return v_res_5485_;
}
pub unsafe fn l_List_insertIdx(
    mut v_00_u03b1_5486_: *mut leanh::LeanObject,
    mut v_xs_5487_: *mut leanh::LeanObject,
    mut v_i_5488_: *mut leanh::LeanObject,
    mut v_a_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5489_, v_i_5488_, v_xs_5487_,
    );
    return v___x_5490_;
}
pub unsafe fn l_List_insertIdx___boxed(
    mut v_00_u03b1_5491_: *mut leanh::LeanObject,
    mut v_xs_5492_: *mut leanh::LeanObject,
    mut v_i_5493_: *mut leanh::LeanObject,
    mut v_a_5494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5495_ = l_List_insertIdx(v_00_u03b1_5491_, v_xs_5492_, v_i_5493_, v_a_5494_);
    leanh::lean_dec(v_i_5493_);
    return v_res_5495_;
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(
    mut v_00_u03b1_5496_: *mut leanh::LeanObject,
    mut v_a_5497_: *mut leanh::LeanObject,
    mut v_a_5498_: *mut leanh::LeanObject,
    mut v_a_5499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5500_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___redArg(
        v_a_5497_, v_a_5498_, v_a_5499_,
    );
    return v___x_5500_;
}
pub unsafe fn l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0___boxed(
    mut v_00_u03b1_5501_: *mut leanh::LeanObject,
    mut v_a_5502_: *mut leanh::LeanObject,
    mut v_a_5503_: *mut leanh::LeanObject,
    mut v_a_5504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5505_ = l_List_modifyTailIdx_go___at___00List_insertIdx_spec__0(
        v_00_u03b1_5501_,
        v_a_5502_,
        v_a_5503_,
        v_a_5504_,
    );
    leanh::lean_dec(v_a_5503_);
    return v_res_5505_;
}
pub unsafe fn l_List_erase___redArg(
    mut v_inst_5506_: *mut leanh::LeanObject,
    mut v_x_5507_: *mut leanh::LeanObject,
    mut v_x_5508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5507_) == 0 {
                    leanh::lean_dec(v_x_5508_);
                    leanh::lean_dec_ref(v_inst_5506_);
                    return v_x_5507_;
                } else {
                    v_head_5509_ = leanh::lean_ctor_get(v_x_5507_, 0);
                    v_tail_5510_ = leanh::lean_ctor_get(v_x_5507_, 1);
                    v_isSharedCheck_5520_ = (!leanh::lean_is_exclusive(v_x_5507_)) as u8;
                    if v_isSharedCheck_5520_ == 0 {
                        v___x_5512_ = v_x_5507_;
                        v_isShared_5513_ = v_isSharedCheck_5520_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5510_);
                        leanh::lean_inc(v_head_5509_);
                        leanh::lean_dec(v_x_5507_);
                        v___x_5512_ = leanh::lean_box(0);
                        v_isShared_5513_ = v_isSharedCheck_5520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_5506_);
                leanh::lean_inc(v_x_5508_);
                leanh::lean_inc(v_head_5509_);
                v___x_5514_ = leanh::lean_apply_2(v_inst_5506_, v_head_5509_, v_x_5508_);
                v___x_5515_ = (leanh::lean_unbox(v___x_5514_) as u8);
                if v___x_5515_ == 0 {
                    v___x_5516_ = l_List_erase___redArg(v_inst_5506_, v_tail_5510_, v_x_5508_);
                    if v_isShared_5513_ == 0 {
                        leanh::lean_ctor_set(v___x_5512_, 1, v___x_5516_);
                        v___x_5518_ = v___x_5512_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5519_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_head_5509_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5516_);
                        v___x_5518_ = v_reuseFailAlloc_5519_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5512_);
                    leanh::lean_dec(v_head_5509_);
                    leanh::lean_dec(v_x_5508_);
                    leanh::lean_dec_ref(v_inst_5506_);
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
    mut v_00_u03b1_5521_: *mut leanh::LeanObject,
    mut v_inst_5522_: *mut leanh::LeanObject,
    mut v_x_5523_: *mut leanh::LeanObject,
    mut v_x_5524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5525_ = l_List_erase___redArg(v_inst_5522_, v_x_5523_, v_x_5524_);
    return v___x_5525_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter___redArg(
    mut v_x_5526_: *mut leanh::LeanObject,
    mut v_x_5527_: *mut leanh::LeanObject,
    mut v_h__1_5528_: *mut leanh::LeanObject,
    mut v_h__2_5529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5526_) == 0 {
        let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_5529_);
        v___x_5530_ = leanh::lean_apply_1(v_h__1_5528_, v_x_5527_);
        return v___x_5530_;
    } else {
        let mut v_head_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_5528_);
        v_head_5531_ = leanh::lean_ctor_get(v_x_5526_, 0);
        leanh::lean_inc(v_head_5531_);
        v_tail_5532_ = leanh::lean_ctor_get(v_x_5526_, 1);
        leanh::lean_inc(v_tail_5532_);
        leanh::lean_dec_ref_known(v_x_5526_, 2);
        v___x_5533_ =
            leanh::lean_apply_3(v_h__2_5529_, v_head_5531_, v_tail_5532_, v_x_5527_);
        return v___x_5533_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_getLastD_match__1_splitter(
    mut v_00_u03b1_5534_: *mut leanh::LeanObject,
    mut v_motive_5535_: *mut leanh::LeanObject,
    mut v_x_5536_: *mut leanh::LeanObject,
    mut v_x_5537_: *mut leanh::LeanObject,
    mut v_h__1_5538_: *mut leanh::LeanObject,
    mut v_h__2_5539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5536_) == 0 {
        let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_5539_);
        v___x_5540_ = leanh::lean_apply_1(v_h__1_5538_, v_x_5537_);
        return v___x_5540_;
    } else {
        let mut v_head_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_5538_);
        v_head_5541_ = leanh::lean_ctor_get(v_x_5536_, 0);
        leanh::lean_inc(v_head_5541_);
        v_tail_5542_ = leanh::lean_ctor_get(v_x_5536_, 1);
        leanh::lean_inc(v_tail_5542_);
        leanh::lean_dec_ref_known(v_x_5536_, 2);
        v___x_5543_ =
            leanh::lean_apply_3(v_h__2_5539_, v_head_5541_, v_tail_5542_, v_x_5537_);
        return v___x_5543_;
    }
}
pub unsafe fn l_List_eraseP___redArg(
    mut v_p_5544_: *mut leanh::LeanObject,
    mut v_x_5545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5545_) == 0 {
                    leanh::lean_dec_ref(v_p_5544_);
                    return v_x_5545_;
                } else {
                    v_head_5546_ = leanh::lean_ctor_get(v_x_5545_, 0);
                    v_tail_5547_ = leanh::lean_ctor_get(v_x_5545_, 1);
                    v_isSharedCheck_5557_ = (!leanh::lean_is_exclusive(v_x_5545_)) as u8;
                    if v_isSharedCheck_5557_ == 0 {
                        v___x_5549_ = v_x_5545_;
                        v_isShared_5550_ = v_isSharedCheck_5557_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5547_);
                        leanh::lean_inc(v_head_5546_);
                        leanh::lean_dec(v_x_5545_);
                        v___x_5549_ = leanh::lean_box(0);
                        v_isShared_5550_ = v_isSharedCheck_5557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_p_5544_);
                leanh::lean_inc(v_head_5546_);
                v___x_5551_ = leanh::lean_apply_1(v_p_5544_, v_head_5546_);
                v___x_5552_ = (leanh::lean_unbox(v___x_5551_) as u8);
                if v___x_5552_ == 0 {
                    v___x_5553_ = l_List_eraseP___redArg(v_p_5544_, v_tail_5547_);
                    if v_isShared_5550_ == 0 {
                        leanh::lean_ctor_set(v___x_5549_, 1, v___x_5553_);
                        v___x_5555_ = v___x_5549_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5556_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_head_5546_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5553_);
                        v___x_5555_ = v_reuseFailAlloc_5556_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5549_);
                    leanh::lean_dec(v_head_5546_);
                    leanh::lean_dec_ref(v_p_5544_);
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
    mut v_00_u03b1_5558_: *mut leanh::LeanObject,
    mut v_p_5559_: *mut leanh::LeanObject,
    mut v_x_5560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5561_ = l_List_eraseP___redArg(v_p_5559_, v_x_5560_);
    return v___x_5561_;
}
pub unsafe fn l_List_eraseIdx___redArg(
    mut v_x_5562_: *mut leanh::LeanObject,
    mut v_x_5563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v_zero_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5570_: u8 = 0;
    let mut v_one_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5562_) == 0 {
                    return v_x_5562_;
                } else {
                    v_head_5564_ = leanh::lean_ctor_get(v_x_5562_, 0);
                    v_tail_5565_ = leanh::lean_ctor_get(v_x_5562_, 1);
                    v_isSharedCheck_5577_ = (!leanh::lean_is_exclusive(v_x_5562_)) as u8;
                    if v_isSharedCheck_5577_ == 0 {
                        v___x_5567_ = v_x_5562_;
                        v_isShared_5568_ = v_isSharedCheck_5577_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5565_);
                        leanh::lean_inc(v_head_5564_);
                        leanh::lean_dec(v_x_5562_);
                        v___x_5567_ = leanh::lean_box(0);
                        v_isShared_5568_ = v_isSharedCheck_5577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_5569_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5570_ = lean_nat_dec_eq(v_x_5563_, v_zero_5569_);
                if v_isZero_5570_ == 1 {
                    leanh::lean_del_object(v___x_5567_);
                    leanh::lean_dec(v_head_5564_);
                    return v_tail_5565_;
                } else {
                    v_one_5571_ = leanh::lean_unsigned_to_nat(1);
                    v_n_5572_ = lean_nat_sub(v_x_5563_, v_one_5571_);
                    v___x_5573_ = l_List_eraseIdx___redArg(v_tail_5565_, v_n_5572_);
                    leanh::lean_dec(v_n_5572_);
                    if v_isShared_5568_ == 0 {
                        leanh::lean_ctor_set(v___x_5567_, 1, v___x_5573_);
                        v___x_5575_ = v___x_5567_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5576_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_head_5564_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5573_);
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
    mut v_x_5578_: *mut leanh::LeanObject,
    mut v_x_5579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5580_ = l_List_eraseIdx___redArg(v_x_5578_, v_x_5579_);
    leanh::lean_dec(v_x_5579_);
    return v_res_5580_;
}
pub unsafe fn l_List_eraseIdx(
    mut v_00_u03b1_5581_: *mut leanh::LeanObject,
    mut v_x_5582_: *mut leanh::LeanObject,
    mut v_x_5583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5584_ = l_List_eraseIdx___redArg(v_x_5582_, v_x_5583_);
    return v___x_5584_;
}
pub unsafe fn l_List_eraseIdx___boxed(
    mut v_00_u03b1_5585_: *mut leanh::LeanObject,
    mut v_x_5586_: *mut leanh::LeanObject,
    mut v_x_5587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5588_ = l_List_eraseIdx(v_00_u03b1_5585_, v_x_5586_, v_x_5587_);
    leanh::lean_dec(v_x_5587_);
    return v_res_5588_;
}
pub unsafe fn l_List_find_x3f___redArg(
    mut v_p_5589_: *mut leanh::LeanObject,
    mut v_x_5590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: u8 = 0;
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5590_) == 0 {
                    leanh::lean_dec_ref(v_p_5589_);
                    v___x_5591_ = leanh::lean_box(0);
                    return v___x_5591_;
                } else {
                    v_head_5592_ = leanh::lean_ctor_get(v_x_5590_, 0);
                    leanh::lean_inc_n(v_head_5592_, 2);
                    v_tail_5593_ = leanh::lean_ctor_get(v_x_5590_, 1);
                    leanh::lean_inc(v_tail_5593_);
                    leanh::lean_dec_ref_known(v_x_5590_, 2);
                    leanh::lean_inc_ref(v_p_5589_);
                    v___x_5594_ = leanh::lean_apply_1(v_p_5589_, v_head_5592_);
                    v___x_5595_ = (leanh::lean_unbox(v___x_5594_) as u8);
                    if v___x_5595_ == 0 {
                        leanh::lean_dec(v_head_5592_);
                        v_x_5590_ = v_tail_5593_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5593_);
                        leanh::lean_dec_ref(v_p_5589_);
                        v___x_5597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5597_, 0, v_head_5592_);
                        return v___x_5597_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f(
    mut v_00_u03b1_5598_: *mut leanh::LeanObject,
    mut v_p_5599_: *mut leanh::LeanObject,
    mut v_x_5600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5601_ = l_List_find_x3f___redArg(v_p_5599_, v_x_5600_);
    return v___x_5601_;
}
pub unsafe fn l_List_findSome_x3f___redArg(
    mut v_f_5602_: *mut leanh::LeanObject,
    mut v_x_5603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5603_) == 0 {
                    leanh::lean_dec_ref(v_f_5602_);
                    v___x_5604_ = leanh::lean_box(0);
                    return v___x_5604_;
                } else {
                    v_head_5605_ = leanh::lean_ctor_get(v_x_5603_, 0);
                    leanh::lean_inc(v_head_5605_);
                    v_tail_5606_ = leanh::lean_ctor_get(v_x_5603_, 1);
                    leanh::lean_inc(v_tail_5606_);
                    leanh::lean_dec_ref_known(v_x_5603_, 2);
                    leanh::lean_inc_ref(v_f_5602_);
                    v___x_5607_ = leanh::lean_apply_1(v_f_5602_, v_head_5605_);
                    if leanh::lean_obj_tag(v___x_5607_) == 0 {
                        v_x_5603_ = v_tail_5606_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5606_);
                        leanh::lean_dec_ref(v_f_5602_);
                        return v___x_5607_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findSome_x3f(
    mut v_00_u03b1_5609_: *mut leanh::LeanObject,
    mut v_00_u03b2_5610_: *mut leanh::LeanObject,
    mut v_f_5611_: *mut leanh::LeanObject,
    mut v_x_5612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_List_findSome_x3f___redArg(v_f_5611_, v_x_5612_);
    return v___x_5613_;
}
pub unsafe fn l_List_findRev_x3f___redArg(
    mut v_p_5614_: *mut leanh::LeanObject,
    mut v_x_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5615_) == 0 {
        let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_p_5614_);
        v___x_5616_ = leanh::lean_box(0);
        return v___x_5616_;
    } else {
        let mut v_head_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_5617_ = leanh::lean_ctor_get(v_x_5615_, 0);
        leanh::lean_inc(v_head_5617_);
        v_tail_5618_ = leanh::lean_ctor_get(v_x_5615_, 1);
        leanh::lean_inc(v_tail_5618_);
        leanh::lean_dec_ref_known(v_x_5615_, 2);
        leanh::lean_inc_ref(v_p_5614_);
        v___x_5619_ = l_List_findRev_x3f___redArg(v_p_5614_, v_tail_5618_);
        if leanh::lean_obj_tag(v___x_5619_) == 0 {
            let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5621_: u8 = 0;
            leanh::lean_inc(v_head_5617_);
            v___x_5620_ = leanh::lean_apply_1(v_p_5614_, v_head_5617_);
            v___x_5621_ = (leanh::lean_unbox(v___x_5620_) as u8);
            if v___x_5621_ == 0 {
                leanh::lean_dec(v_head_5617_);
                return v___x_5619_;
            } else {
                let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5622_, 0, v_head_5617_);
                return v___x_5622_;
            }
        } else {
            leanh::lean_dec(v_head_5617_);
            leanh::lean_dec_ref(v_p_5614_);
            return v___x_5619_;
        }
    }
}
pub unsafe fn l_List_findRev_x3f(
    mut v_00_u03b1_5623_: *mut leanh::LeanObject,
    mut v_p_5624_: *mut leanh::LeanObject,
    mut v_x_5625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5626_ = l_List_findRev_x3f___redArg(v_p_5624_, v_x_5625_);
    return v___x_5626_;
}
pub unsafe fn l_List_findSomeRev_x3f___redArg(
    mut v_f_5627_: *mut leanh::LeanObject,
    mut v_x_5628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5628_) == 0 {
        let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_5627_);
        v___x_5629_ = leanh::lean_box(0);
        return v___x_5629_;
    } else {
        let mut v_head_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_5630_ = leanh::lean_ctor_get(v_x_5628_, 0);
        leanh::lean_inc(v_head_5630_);
        v_tail_5631_ = leanh::lean_ctor_get(v_x_5628_, 1);
        leanh::lean_inc(v_tail_5631_);
        leanh::lean_dec_ref_known(v_x_5628_, 2);
        leanh::lean_inc_ref(v_f_5627_);
        v___x_5632_ = l_List_findSomeRev_x3f___redArg(v_f_5627_, v_tail_5631_);
        if leanh::lean_obj_tag(v___x_5632_) == 0 {
            let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5633_ = leanh::lean_apply_1(v_f_5627_, v_head_5630_);
            return v___x_5633_;
        } else {
            leanh::lean_dec(v_head_5630_);
            leanh::lean_dec_ref(v_f_5627_);
            return v___x_5632_;
        }
    }
}
pub unsafe fn l_List_findSomeRev_x3f(
    mut v_00_u03b1_5634_: *mut leanh::LeanObject,
    mut v_00_u03b2_5635_: *mut leanh::LeanObject,
    mut v_f_5636_: *mut leanh::LeanObject,
    mut v_x_5637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5638_ = l_List_findSomeRev_x3f___redArg(v_f_5636_, v_x_5637_);
    return v___x_5638_;
}
pub unsafe fn l_List_findIdx_go___redArg(
    mut v_p_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
    mut v_a_5641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5640_) == 0 {
                    leanh::lean_dec_ref(v_p_5639_);
                    return v_a_5641_;
                } else {
                    v_head_5642_ = leanh::lean_ctor_get(v_a_5640_, 0);
                    leanh::lean_inc(v_head_5642_);
                    v_tail_5643_ = leanh::lean_ctor_get(v_a_5640_, 1);
                    leanh::lean_inc(v_tail_5643_);
                    leanh::lean_dec_ref_known(v_a_5640_, 2);
                    leanh::lean_inc_ref(v_p_5639_);
                    v___x_5644_ = leanh::lean_apply_1(v_p_5639_, v_head_5642_);
                    v___x_5645_ = (leanh::lean_unbox(v___x_5644_) as u8);
                    if v___x_5645_ == 0 {
                        v___x_5646_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5647_ = lean_nat_add(v_a_5641_, v___x_5646_);
                        leanh::lean_dec(v_a_5641_);
                        v_a_5640_ = v_tail_5643_;
                        v_a_5641_ = v___x_5647_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5643_);
                        leanh::lean_dec_ref(v_p_5639_);
                        return v_a_5641_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findIdx_go(
    mut v_00_u03b1_5649_: *mut leanh::LeanObject,
    mut v_p_5650_: *mut leanh::LeanObject,
    mut v_a_5651_: *mut leanh::LeanObject,
    mut v_a_5652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5653_ = l_List_findIdx_go___redArg(v_p_5650_, v_a_5651_, v_a_5652_);
    return v___x_5653_;
}
pub unsafe fn l_List_findIdx___redArg(
    mut v_p_5654_: *mut leanh::LeanObject,
    mut v_l_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5656_ = leanh::lean_unsigned_to_nat(0);
    v___x_5657_ = l_List_findIdx_go___redArg(v_p_5654_, v_l_5655_, v___x_5656_);
    return v___x_5657_;
}
pub unsafe fn l_List_findIdx(
    mut v_00_u03b1_5658_: *mut leanh::LeanObject,
    mut v_p_5659_: *mut leanh::LeanObject,
    mut v_l_5660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5661_ = leanh::lean_unsigned_to_nat(0);
    v___x_5662_ = l_List_findIdx_go___redArg(v_p_5659_, v_l_5660_, v___x_5661_);
    return v___x_5662_;
}
pub unsafe fn l_List_idxOf___redArg___lam__0(
    mut v_inst_5663_: *mut leanh::LeanObject,
    mut v_a_5664_: *mut leanh::LeanObject,
    mut v_x_5665_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    v___x_5666_ = leanh::lean_apply_2(v_inst_5663_, v_x_5665_, v_a_5664_);
    v___x_5667_ = (leanh::lean_unbox(v___x_5666_) as u8);
    return v___x_5667_;
}
pub unsafe fn l_List_idxOf___redArg___lam__0___boxed(
    mut v_inst_5668_: *mut leanh::LeanObject,
    mut v_a_5669_: *mut leanh::LeanObject,
    mut v_x_5670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5671_: u8 = 0;
    let mut v_r_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5671_ = l_List_idxOf___redArg___lam__0(v_inst_5668_, v_a_5669_, v_x_5670_);
    v_r_5672_ = leanh::lean_box((v_res_5671_) as usize);
    return v_r_5672_;
}
pub unsafe fn l_List_idxOf___redArg(
    mut v_inst_5673_: *mut leanh::LeanObject,
    mut v_a_5674_: *mut leanh::LeanObject,
    mut v_l_5675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5676_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5676_, 0, v_inst_5673_);
    leanh::lean_closure_set(v___f_5676_, 1, v_a_5674_);
    v___x_5677_ = leanh::lean_unsigned_to_nat(0);
    v___x_5678_ = l_List_findIdx_go___redArg(v___f_5676_, v_l_5675_, v___x_5677_);
    return v___x_5678_;
}
pub unsafe fn l_List_idxOf(
    mut v_00_u03b1_5679_: *mut leanh::LeanObject,
    mut v_inst_5680_: *mut leanh::LeanObject,
    mut v_a_5681_: *mut leanh::LeanObject,
    mut v_l_5682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5683_ = l_List_idxOf___redArg(v_inst_5680_, v_a_5681_, v_l_5682_);
    return v___x_5683_;
}
pub unsafe fn l_List_findIdx_x3f_go___redArg(
    mut v_p_5684_: *mut leanh::LeanObject,
    mut v_a_5685_: *mut leanh::LeanObject,
    mut v_a_5686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: u8 = 0;
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5685_) == 0 {
                    leanh::lean_dec(v_a_5686_);
                    leanh::lean_dec_ref(v_p_5684_);
                    v___x_5687_ = leanh::lean_box(0);
                    return v___x_5687_;
                } else {
                    v_head_5688_ = leanh::lean_ctor_get(v_a_5685_, 0);
                    leanh::lean_inc(v_head_5688_);
                    v_tail_5689_ = leanh::lean_ctor_get(v_a_5685_, 1);
                    leanh::lean_inc(v_tail_5689_);
                    leanh::lean_dec_ref_known(v_a_5685_, 2);
                    leanh::lean_inc_ref(v_p_5684_);
                    v___x_5690_ = leanh::lean_apply_1(v_p_5684_, v_head_5688_);
                    v___x_5691_ = (leanh::lean_unbox(v___x_5690_) as u8);
                    if v___x_5691_ == 0 {
                        v___x_5692_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5693_ = lean_nat_add(v_a_5686_, v___x_5692_);
                        leanh::lean_dec(v_a_5686_);
                        v_a_5685_ = v_tail_5689_;
                        v_a_5686_ = v___x_5693_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5689_);
                        leanh::lean_dec_ref(v_p_5684_);
                        v___x_5695_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5695_, 0, v_a_5686_);
                        return v___x_5695_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findIdx_x3f_go(
    mut v_00_u03b1_5696_: *mut leanh::LeanObject,
    mut v_p_5697_: *mut leanh::LeanObject,
    mut v_a_5698_: *mut leanh::LeanObject,
    mut v_a_5699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l_List_findIdx_x3f_go___redArg(v_p_5697_, v_a_5698_, v_a_5699_);
    return v___x_5700_;
}
pub unsafe fn l_List_findIdx_x3f___redArg(
    mut v_p_5701_: *mut leanh::LeanObject,
    mut v_l_5702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = leanh::lean_unsigned_to_nat(0);
    v___x_5704_ = l_List_findIdx_x3f_go___redArg(v_p_5701_, v_l_5702_, v___x_5703_);
    return v___x_5704_;
}
pub unsafe fn l_List_findIdx_x3f(
    mut v_00_u03b1_5705_: *mut leanh::LeanObject,
    mut v_p_5706_: *mut leanh::LeanObject,
    mut v_l_5707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5708_ = leanh::lean_unsigned_to_nat(0);
    v___x_5709_ = l_List_findIdx_x3f_go___redArg(v_p_5706_, v_l_5707_, v___x_5708_);
    return v___x_5709_;
}
pub unsafe fn l_List_idxOf_x3f___redArg(
    mut v_inst_5710_: *mut leanh::LeanObject,
    mut v_a_5711_: *mut leanh::LeanObject,
    mut v_l_5712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5713_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5713_, 0, v_inst_5710_);
    leanh::lean_closure_set(v___f_5713_, 1, v_a_5711_);
    v___x_5714_ = leanh::lean_unsigned_to_nat(0);
    v___x_5715_ = l_List_findIdx_x3f_go___redArg(v___f_5713_, v_l_5712_, v___x_5714_);
    return v___x_5715_;
}
pub unsafe fn l_List_idxOf_x3f(
    mut v_00_u03b1_5716_: *mut leanh::LeanObject,
    mut v_inst_5717_: *mut leanh::LeanObject,
    mut v_a_5718_: *mut leanh::LeanObject,
    mut v_l_5719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5720_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5720_, 0, v_inst_5717_);
    leanh::lean_closure_set(v___f_5720_, 1, v_a_5718_);
    v___x_5721_ = leanh::lean_unsigned_to_nat(0);
    v___x_5722_ = l_List_findIdx_x3f_go___redArg(v___f_5720_, v_l_5719_, v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn l_List_findFinIdx_x3f_go___redArg(
    mut v_p_5723_: *mut leanh::LeanObject,
    mut v_l_x27_5724_: *mut leanh::LeanObject,
    mut v_i_5725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: u8 = 0;
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_x27_5724_) == 0 {
                    leanh::lean_dec(v_i_5725_);
                    leanh::lean_dec_ref(v_p_5723_);
                    v___x_5726_ = leanh::lean_box(0);
                    return v___x_5726_;
                } else {
                    v_head_5727_ = leanh::lean_ctor_get(v_l_x27_5724_, 0);
                    leanh::lean_inc(v_head_5727_);
                    v_tail_5728_ = leanh::lean_ctor_get(v_l_x27_5724_, 1);
                    leanh::lean_inc(v_tail_5728_);
                    leanh::lean_dec_ref_known(v_l_x27_5724_, 2);
                    leanh::lean_inc_ref(v_p_5723_);
                    v___x_5729_ = leanh::lean_apply_1(v_p_5723_, v_head_5727_);
                    v___x_5730_ = (leanh::lean_unbox(v___x_5729_) as u8);
                    if v___x_5730_ == 0 {
                        v___x_5731_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5732_ = lean_nat_add(v_i_5725_, v___x_5731_);
                        leanh::lean_dec(v_i_5725_);
                        v_l_x27_5724_ = v_tail_5728_;
                        v_i_5725_ = v___x_5732_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5728_);
                        leanh::lean_dec_ref(v_p_5723_);
                        v___x_5734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5734_, 0, v_i_5725_);
                        return v___x_5734_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findFinIdx_x3f_go(
    mut v_00_u03b1_5735_: *mut leanh::LeanObject,
    mut v_p_5736_: *mut leanh::LeanObject,
    mut v_l_5737_: *mut leanh::LeanObject,
    mut v_l_x27_5738_: *mut leanh::LeanObject,
    mut v_i_5739_: *mut leanh::LeanObject,
    mut v_h_5740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ = l_List_findFinIdx_x3f_go___redArg(v_p_5736_, v_l_x27_5738_, v_i_5739_);
    return v___x_5741_;
}
pub unsafe fn l_List_findFinIdx_x3f_go___boxed(
    mut v_00_u03b1_5742_: *mut leanh::LeanObject,
    mut v_p_5743_: *mut leanh::LeanObject,
    mut v_l_5744_: *mut leanh::LeanObject,
    mut v_l_x27_5745_: *mut leanh::LeanObject,
    mut v_i_5746_: *mut leanh::LeanObject,
    mut v_h_5747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_List_findFinIdx_x3f_go(
        v_00_u03b1_5742_,
        v_p_5743_,
        v_l_5744_,
        v_l_x27_5745_,
        v_i_5746_,
        v_h_5747_,
    );
    leanh::lean_dec(v_l_5744_);
    return v_res_5748_;
}
pub unsafe fn l_List_findFinIdx_x3f___redArg(
    mut v_p_5749_: *mut leanh::LeanObject,
    mut v_l_5750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = leanh::lean_unsigned_to_nat(0);
    v___x_5752_ = l_List_findFinIdx_x3f_go___redArg(v_p_5749_, v_l_5750_, v___x_5751_);
    return v___x_5752_;
}
pub unsafe fn l_List_findFinIdx_x3f(
    mut v_00_u03b1_5753_: *mut leanh::LeanObject,
    mut v_p_5754_: *mut leanh::LeanObject,
    mut v_l_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = leanh::lean_unsigned_to_nat(0);
    v___x_5757_ = l_List_findFinIdx_x3f_go___redArg(v_p_5754_, v_l_5755_, v___x_5756_);
    return v___x_5757_;
}
pub unsafe fn l_List_finIdxOf_x3f___redArg(
    mut v_inst_5758_: *mut leanh::LeanObject,
    mut v_a_5759_: *mut leanh::LeanObject,
    mut v_l_5760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5761_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5761_, 0, v_inst_5758_);
    leanh::lean_closure_set(v___f_5761_, 1, v_a_5759_);
    v___x_5762_ = leanh::lean_unsigned_to_nat(0);
    v___x_5763_ = l_List_findFinIdx_x3f_go___redArg(v___f_5761_, v_l_5760_, v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn l_List_finIdxOf_x3f(
    mut v_00_u03b1_5764_: *mut leanh::LeanObject,
    mut v_inst_5765_: *mut leanh::LeanObject,
    mut v_a_5766_: *mut leanh::LeanObject,
    mut v_l_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5768_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5768_, 0, v_inst_5765_);
    leanh::lean_closure_set(v___f_5768_, 1, v_a_5766_);
    v___x_5769_ = leanh::lean_unsigned_to_nat(0);
    v___x_5770_ = l_List_findFinIdx_x3f_go___redArg(v___f_5768_, v_l_5767_, v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l_List_countP_go___redArg(
    mut v_p_5771_: *mut leanh::LeanObject,
    mut v_a_5772_: *mut leanh::LeanObject,
    mut v_a_5773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5772_) == 0 {
                    leanh::lean_dec_ref(v_p_5771_);
                    return v_a_5773_;
                } else {
                    v_head_5774_ = leanh::lean_ctor_get(v_a_5772_, 0);
                    leanh::lean_inc(v_head_5774_);
                    v_tail_5775_ = leanh::lean_ctor_get(v_a_5772_, 1);
                    leanh::lean_inc(v_tail_5775_);
                    leanh::lean_dec_ref_known(v_a_5772_, 2);
                    leanh::lean_inc_ref(v_p_5771_);
                    v___x_5776_ = leanh::lean_apply_1(v_p_5771_, v_head_5774_);
                    v___x_5777_ = (leanh::lean_unbox(v___x_5776_) as u8);
                    if v___x_5777_ == 0 {
                        v_a_5772_ = v_tail_5775_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5779_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5780_ = lean_nat_add(v_a_5773_, v___x_5779_);
                        leanh::lean_dec(v_a_5773_);
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
    mut v_00_u03b1_5782_: *mut leanh::LeanObject,
    mut v_p_5783_: *mut leanh::LeanObject,
    mut v_a_5784_: *mut leanh::LeanObject,
    mut v_a_5785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5786_ = l_List_countP_go___redArg(v_p_5783_, v_a_5784_, v_a_5785_);
    return v___x_5786_;
}
pub unsafe fn l_List_countP___redArg(
    mut v_p_5787_: *mut leanh::LeanObject,
    mut v_l_5788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5789_ = leanh::lean_unsigned_to_nat(0);
    v___x_5790_ = l_List_countP_go___redArg(v_p_5787_, v_l_5788_, v___x_5789_);
    return v___x_5790_;
}
pub unsafe fn l_List_countP(
    mut v_00_u03b1_5791_: *mut leanh::LeanObject,
    mut v_p_5792_: *mut leanh::LeanObject,
    mut v_l_5793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5794_ = leanh::lean_unsigned_to_nat(0);
    v___x_5795_ = l_List_countP_go___redArg(v_p_5792_, v_l_5793_, v___x_5794_);
    return v___x_5795_;
}
pub unsafe fn l_List_count___redArg(
    mut v_inst_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
    mut v_l_5798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5799_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5799_, 0, v_inst_5796_);
    leanh::lean_closure_set(v___f_5799_, 1, v_a_5797_);
    v___x_5800_ = leanh::lean_unsigned_to_nat(0);
    v___x_5801_ = l_List_countP_go___redArg(v___f_5799_, v_l_5798_, v___x_5800_);
    return v___x_5801_;
}
pub unsafe fn l_List_count(
    mut v_00_u03b1_5802_: *mut leanh::LeanObject,
    mut v_inst_5803_: *mut leanh::LeanObject,
    mut v_a_5804_: *mut leanh::LeanObject,
    mut v_l_5805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5806_ = leanh::lean_alloc_closure(
        l_List_idxOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5806_, 0, v_inst_5803_);
    leanh::lean_closure_set(v___f_5806_, 1, v_a_5804_);
    v___x_5807_ = leanh::lean_unsigned_to_nat(0);
    v___x_5808_ = l_List_countP_go___redArg(v___f_5806_, v_l_5805_, v___x_5807_);
    return v___x_5808_;
}
pub unsafe fn l_List_lookup___redArg(
    mut v_inst_5809_: *mut leanh::LeanObject,
    mut v_x_5810_: *mut leanh::LeanObject,
    mut v_x_5811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: u8 = 0;
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5811_) == 0 {
                    leanh::lean_dec(v_x_5810_);
                    leanh::lean_dec_ref(v_inst_5809_);
                    v___x_5812_ = leanh::lean_box(0);
                    return v___x_5812_;
                } else {
                    v_head_5813_ = leanh::lean_ctor_get(v_x_5811_, 0);
                    leanh::lean_inc(v_head_5813_);
                    v_tail_5814_ = leanh::lean_ctor_get(v_x_5811_, 1);
                    leanh::lean_inc(v_tail_5814_);
                    leanh::lean_dec_ref_known(v_x_5811_, 2);
                    v_fst_5815_ = leanh::lean_ctor_get(v_head_5813_, 0);
                    leanh::lean_inc(v_fst_5815_);
                    v_snd_5816_ = leanh::lean_ctor_get(v_head_5813_, 1);
                    leanh::lean_inc(v_snd_5816_);
                    leanh::lean_dec(v_head_5813_);
                    leanh::lean_inc_ref(v_inst_5809_);
                    leanh::lean_inc(v_x_5810_);
                    v___x_5817_ = leanh::lean_apply_2(v_inst_5809_, v_x_5810_, v_fst_5815_);
                    v___x_5818_ = (leanh::lean_unbox(v___x_5817_) as u8);
                    if v___x_5818_ == 0 {
                        leanh::lean_dec(v_snd_5816_);
                        v_x_5811_ = v_tail_5814_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5814_);
                        leanh::lean_dec(v_x_5810_);
                        leanh::lean_dec_ref(v_inst_5809_);
                        v___x_5820_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5820_, 0, v_snd_5816_);
                        return v___x_5820_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lookup(
    mut v_00_u03b1_5821_: *mut leanh::LeanObject,
    mut v_00_u03b2_5822_: *mut leanh::LeanObject,
    mut v_inst_5823_: *mut leanh::LeanObject,
    mut v_x_5824_: *mut leanh::LeanObject,
    mut v_x_5825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5826_ = l_List_lookup___redArg(v_inst_5823_, v_x_5824_, v_x_5825_);
    return v___x_5826_;
}
pub unsafe fn _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5844_ =
        l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__0;
    v___x_5845_ = l_String_toRawSubstring_x27(v___x_5844_);
    return v___x_5845_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(
    mut v_x_5865_: *mut leanh::LeanObject,
    mut v_a_5866_: *mut leanh::LeanObject,
    mut v_a_5867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: u8 = 0;
    v___x_5868_ = l_List_term___x7e___00__closed__1;
    leanh::lean_inc(v_x_5865_);
    v___x_5869_ = l_Lean_Syntax_isOfKind(v_x_5865_, v___x_5868_);
    if v___x_5869_ == 0 {
        let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5865_);
        v___x_5870_ = leanh::lean_box(1);
        v___x_5871_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5871_, 0, v___x_5870_);
        leanh::lean_ctor_set(v___x_5871_, 1, v_a_5867_);
        return v___x_5871_;
    } else {
        let mut v_quotContext_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5879_: u8 = 0;
        let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_5872_ = leanh::lean_ctor_get(v_a_5866_, 1);
        v_currMacroScope_5873_ = leanh::lean_ctor_get(v_a_5866_, 2);
        v_ref_5874_ = leanh::lean_ctor_get(v_a_5866_, 5);
        v___x_5875_ = leanh::lean_unsigned_to_nat(0);
        v___x_5876_ = l_Lean_Syntax_getArg(v_x_5865_, v___x_5875_);
        v___x_5877_ = leanh::lean_unsigned_to_nat(2);
        v___x_5878_ = l_Lean_Syntax_getArg(v_x_5865_, v___x_5877_);
        leanh::lean_dec(v_x_5865_);
        v___x_5879_ = 0;
        v___x_5880_ = l_Lean_SourceInfo_fromRef(v_ref_5874_, v___x_5879_);
        v___x_5881_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
        v___x_5882_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1), core::ptr::addr_of_mut!(l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1_once), _init_l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__1);
        v___x_5883_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__2;
        leanh::lean_inc(v_currMacroScope_5873_);
        leanh::lean_inc(v_quotContext_5872_);
        v___x_5884_ =
            l_Lean_addMacroScope(v_quotContext_5872_, v___x_5883_, v_currMacroScope_5873_);
        v___x_5885_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___closed__8;
        leanh::lean_inc_n(v___x_5880_, 2);
        v___x_5886_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_5886_, 0, v___x_5880_);
        leanh::lean_ctor_set(v___x_5886_, 1, v___x_5882_);
        leanh::lean_ctor_set(v___x_5886_, 2, v___x_5884_);
        leanh::lean_ctor_set(v___x_5886_, 3, v___x_5885_);
        v___x_5887_ = l_List_lex___auto__1___closed__9;
        v___x_5888_ = l_Lean_Syntax_node2(v___x_5880_, v___x_5887_, v___x_5876_, v___x_5878_);
        v___x_5889_ = l_Lean_Syntax_node2(v___x_5880_, v___x_5881_, v___x_5886_, v___x_5888_);
        v___x_5890_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5890_, 0, v___x_5889_);
        leanh::lean_ctor_set(v___x_5890_, 1, v_a_5867_);
        return v___x_5890_;
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1___boxed(
    mut v_x_5891_: *mut leanh::LeanObject,
    mut v_a_5892_: *mut leanh::LeanObject,
    mut v_a_5893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5894_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x7e____1(
        v_x_5891_, v_a_5892_, v_a_5893_,
    );
    leanh::lean_dec_ref(v_a_5892_);
    return v_res_5894_;
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(
    mut v_x_5895_: *mut leanh::LeanObject,
    mut v_a_5896_: *mut leanh::LeanObject,
    mut v_a_5897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    v___x_5898_ = l_List___aux__Init__Data__List__Basic______macroRules__List__term___x3c_x2b____1___closed__1;
    leanh::lean_inc(v_x_5895_);
    v___x_5899_ = l_Lean_Syntax_isOfKind(v_x_5895_, v___x_5898_);
    if v___x_5899_ == 0 {
        let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_5895_);
        v___x_5900_ = leanh::lean_box(0);
        v___x_5901_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5901_, 0, v___x_5900_);
        leanh::lean_ctor_set(v___x_5901_, 1, v_a_5897_);
        return v___x_5901_;
    } else {
        let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5905_: u8 = 0;
        v___x_5902_ = leanh::lean_unsigned_to_nat(0);
        v___x_5903_ = l_Lean_Syntax_getArg(v_x_5895_, v___x_5902_);
        v___x_5904_ =
            l_List___aux__Init__Data__List__Basic______unexpand__List__Sublist__1___closed__1;
        leanh::lean_inc(v___x_5903_);
        v___x_5905_ = l_Lean_Syntax_isOfKind(v___x_5903_, v___x_5904_);
        if v___x_5905_ == 0 {
            let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_5903_);
            leanh::lean_dec(v_x_5895_);
            v___x_5906_ = leanh::lean_box(0);
            v___x_5907_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_5907_, 0, v___x_5906_);
            leanh::lean_ctor_set(v___x_5907_, 1, v_a_5897_);
            return v___x_5907_;
        } else {
            let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5911_: u8 = 0;
            v___x_5908_ = leanh::lean_unsigned_to_nat(1);
            v___x_5909_ = l_Lean_Syntax_getArg(v_x_5895_, v___x_5908_);
            leanh::lean_dec(v_x_5895_);
            v___x_5910_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_5909_);
            v___x_5911_ = l_Lean_Syntax_matchesNull(v___x_5909_, v___x_5910_);
            if v___x_5911_ == 0 {
                let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_5909_);
                leanh::lean_dec(v___x_5903_);
                v___x_5912_ = leanh::lean_box(0);
                v___x_5913_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5913_, 0, v___x_5912_);
                leanh::lean_ctor_set(v___x_5913_, 1, v_a_5897_);
                return v___x_5913_;
            } else {
                let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5917_: u8 = 0;
                let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5914_ = l_Lean_Syntax_getArg(v___x_5909_, v___x_5902_);
                v___x_5915_ = l_Lean_Syntax_getArg(v___x_5909_, v___x_5908_);
                leanh::lean_dec(v___x_5909_);
                v_ref_5916_ = l_Lean_replaceRef(v___x_5903_, v_a_5896_);
                leanh::lean_dec(v___x_5903_);
                v___x_5917_ = 0;
                v___x_5918_ = l_Lean_SourceInfo_fromRef(v_ref_5916_, v___x_5917_);
                leanh::lean_dec(v_ref_5916_);
                v___x_5919_ = l_List_term___x7e___00__closed__1;
                v___x_5920_ = l_List_term___x7e___00__closed__2;
                leanh::lean_inc(v___x_5918_);
                v___x_5921_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5921_, 0, v___x_5918_);
                leanh::lean_ctor_set(v___x_5921_, 1, v___x_5920_);
                v___x_5922_ = l_Lean_Syntax_node3(
                    v___x_5918_,
                    v___x_5919_,
                    v___x_5914_,
                    v___x_5921_,
                    v___x_5915_,
                );
                v___x_5923_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5923_, 0, v___x_5922_);
                leanh::lean_ctor_set(v___x_5923_, 1, v_a_5897_);
                return v___x_5923_;
            }
        }
    }
}
pub unsafe fn l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1___boxed(
    mut v_x_5924_: *mut leanh::LeanObject,
    mut v_a_5925_: *mut leanh::LeanObject,
    mut v_a_5926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5927_ = l_List___aux__Init__Data__List__Basic______unexpand__List__Perm__1(
        v_x_5924_, v_a_5925_, v_a_5926_,
    );
    leanh::lean_dec(v_a_5925_);
    return v_res_5927_;
}
pub unsafe fn l_List_isPerm___redArg(
    mut v_inst_5928_: *mut leanh::LeanObject,
    mut v_x_5929_: *mut leanh::LeanObject,
    mut v_x_5930_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5931_: u8 = 0;
    let mut v_head_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: u8 = 0;
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5929_) == 0 {
                    leanh::lean_dec_ref(v_inst_5928_);
                    v___x_5931_ = l_List_isEmpty___redArg(v_x_5930_);
                    leanh::lean_dec(v_x_5930_);
                    return v___x_5931_;
                } else {
                    v_head_5932_ = leanh::lean_ctor_get(v_x_5929_, 0);
                    leanh::lean_inc_n(v_head_5932_, 2);
                    v_tail_5933_ = leanh::lean_ctor_get(v_x_5929_, 1);
                    leanh::lean_inc(v_tail_5933_);
                    leanh::lean_dec_ref_known(v_x_5929_, 2);
                    leanh::lean_inc(v_x_5930_);
                    leanh::lean_inc_ref(v_inst_5928_);
                    v___x_5934_ = l_List_elem___redArg(v_inst_5928_, v_head_5932_, v_x_5930_);
                    if v___x_5934_ == 0 {
                        leanh::lean_dec(v_tail_5933_);
                        leanh::lean_dec(v_head_5932_);
                        leanh::lean_dec(v_x_5930_);
                        leanh::lean_dec_ref(v_inst_5928_);
                        return v___x_5934_;
                    } else {
                        leanh::lean_inc_ref(v_inst_5928_);
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
    mut v_inst_5937_: *mut leanh::LeanObject,
    mut v_x_5938_: *mut leanh::LeanObject,
    mut v_x_5939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5940_: u8 = 0;
    let mut v_r_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_List_isPerm___redArg(v_inst_5937_, v_x_5938_, v_x_5939_);
    v_r_5941_ = leanh::lean_box((v_res_5940_) as usize);
    return v_r_5941_;
}
pub unsafe fn l_List_isPerm(
    mut v_00_u03b1_5942_: *mut leanh::LeanObject,
    mut v_inst_5943_: *mut leanh::LeanObject,
    mut v_x_5944_: *mut leanh::LeanObject,
    mut v_x_5945_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5946_: u8 = 0;
    v___x_5946_ = l_List_isPerm___redArg(v_inst_5943_, v_x_5944_, v_x_5945_);
    return v___x_5946_;
}
pub unsafe fn l_List_isPerm___boxed(
    mut v_00_u03b1_5947_: *mut leanh::LeanObject,
    mut v_inst_5948_: *mut leanh::LeanObject,
    mut v_x_5949_: *mut leanh::LeanObject,
    mut v_x_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5951_: u8 = 0;
    let mut v_r_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5951_ = l_List_isPerm(v_00_u03b1_5947_, v_inst_5948_, v_x_5949_, v_x_5950_);
    v_r_5952_ = leanh::lean_box((v_res_5951_) as usize);
    return v_r_5952_;
}
pub unsafe fn l_List_any___redArg(
    mut v_x_5953_: *mut leanh::LeanObject,
    mut v_x_5954_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5955_: u8 = 0;
    let mut v_head_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5953_) == 0 {
                    leanh::lean_dec_ref(v_x_5954_);
                    v___x_5955_ = 0;
                    return v___x_5955_;
                } else {
                    v_head_5956_ = leanh::lean_ctor_get(v_x_5953_, 0);
                    leanh::lean_inc(v_head_5956_);
                    v_tail_5957_ = leanh::lean_ctor_get(v_x_5953_, 1);
                    leanh::lean_inc(v_tail_5957_);
                    leanh::lean_dec_ref_known(v_x_5953_, 2);
                    leanh::lean_inc_ref(v_x_5954_);
                    v___x_5958_ = leanh::lean_apply_1(v_x_5954_, v_head_5956_);
                    v___x_5959_ = (leanh::lean_unbox(v___x_5958_) as u8);
                    if v___x_5959_ == 0 {
                        v_x_5953_ = v_tail_5957_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_5957_);
                        leanh::lean_dec_ref(v_x_5954_);
                        v___x_5961_ = (leanh::lean_unbox(v___x_5958_) as u8);
                        return v___x_5961_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___redArg___boxed(
    mut v_x_5962_: *mut leanh::LeanObject,
    mut v_x_5963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5964_: u8 = 0;
    let mut v_r_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5964_ = l_List_any___redArg(v_x_5962_, v_x_5963_);
    v_r_5965_ = leanh::lean_box((v_res_5964_) as usize);
    return v_r_5965_;
}
pub unsafe fn l_List_any(
    mut v_00_u03b1_5966_: *mut leanh::LeanObject,
    mut v_x_5967_: *mut leanh::LeanObject,
    mut v_x_5968_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5969_: u8 = 0;
    v___x_5969_ = l_List_any___redArg(v_x_5967_, v_x_5968_);
    return v___x_5969_;
}
pub unsafe fn l_List_any___boxed(
    mut v_00_u03b1_5970_: *mut leanh::LeanObject,
    mut v_x_5971_: *mut leanh::LeanObject,
    mut v_x_5972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5973_: u8 = 0;
    let mut v_r_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5973_ = l_List_any(v_00_u03b1_5970_, v_x_5971_, v_x_5972_);
    v_r_5974_ = leanh::lean_box((v_res_5973_) as usize);
    return v_r_5974_;
}
pub unsafe fn l_List_all___redArg(
    mut v_x_5975_: *mut leanh::LeanObject,
    mut v_x_5976_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5977_: u8 = 0;
    let mut v_head_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v___x_5982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5975_) == 0 {
                    leanh::lean_dec_ref(v_x_5976_);
                    v___x_5977_ = 1;
                    return v___x_5977_;
                } else {
                    v_head_5978_ = leanh::lean_ctor_get(v_x_5975_, 0);
                    leanh::lean_inc(v_head_5978_);
                    v_tail_5979_ = leanh::lean_ctor_get(v_x_5975_, 1);
                    leanh::lean_inc(v_tail_5979_);
                    leanh::lean_dec_ref_known(v_x_5975_, 2);
                    leanh::lean_inc_ref(v_x_5976_);
                    v___x_5980_ = leanh::lean_apply_1(v_x_5976_, v_head_5978_);
                    v___x_5981_ = (leanh::lean_unbox(v___x_5980_) as u8);
                    if v___x_5981_ == 0 {
                        leanh::lean_dec(v_tail_5979_);
                        leanh::lean_dec_ref(v_x_5976_);
                        v___x_5982_ = (leanh::lean_unbox(v___x_5980_) as u8);
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
    mut v_x_5984_: *mut leanh::LeanObject,
    mut v_x_5985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5986_: u8 = 0;
    let mut v_r_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5986_ = l_List_all___redArg(v_x_5984_, v_x_5985_);
    v_r_5987_ = leanh::lean_box((v_res_5986_) as usize);
    return v_r_5987_;
}
pub unsafe fn l_List_all(
    mut v_00_u03b1_5988_: *mut leanh::LeanObject,
    mut v_x_5989_: *mut leanh::LeanObject,
    mut v_x_5990_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5991_: u8 = 0;
    v___x_5991_ = l_List_all___redArg(v_x_5989_, v_x_5990_);
    return v___x_5991_;
}
pub unsafe fn l_List_all___boxed(
    mut v_00_u03b1_5992_: *mut leanh::LeanObject,
    mut v_x_5993_: *mut leanh::LeanObject,
    mut v_x_5994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5995_: u8 = 0;
    let mut v_r_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_List_all(v_00_u03b1_5992_, v_x_5993_, v_x_5994_);
    v_r_5996_ = leanh::lean_box((v_res_5995_) as usize);
    return v_r_5996_;
}
pub unsafe fn l_List_any___at___00List_or_spec__0(
    mut v_x_5997_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5998_: u8 = 0;
    let mut v_head_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: u8 = 0;
    let mut v_tail_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5997_) == 0 {
                    v___x_5998_ = 0;
                    return v___x_5998_;
                } else {
                    v_head_5999_ = leanh::lean_ctor_get(v_x_5997_, 0);
                    v___x_6000_ = (leanh::lean_unbox(v_head_5999_) as u8);
                    if v___x_6000_ == 0 {
                        v_tail_6001_ = leanh::lean_ctor_get(v_x_5997_, 1);
                        v_x_5997_ = v_tail_6001_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6003_ = (leanh::lean_unbox(v_head_5999_) as u8);
                        return v___x_6003_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00List_or_spec__0___boxed(
    mut v_x_6004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6005_: u8 = 0;
    let mut v_r_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_List_any___at___00List_or_spec__0(v_x_6004_);
    leanh::lean_dec(v_x_6004_);
    v_r_6006_ = leanh::lean_box((v_res_6005_) as usize);
    return v_r_6006_;
}
pub unsafe fn l_List_or(mut v_bs_6007_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_6008_: u8 = 0;
    v___x_6008_ = l_List_any___at___00List_or_spec__0(v_bs_6007_);
    return v___x_6008_;
}
pub unsafe fn l_List_or___boxed(
    mut v_bs_6009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6010_: u8 = 0;
    let mut v_r_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6010_ = l_List_or(v_bs_6009_);
    leanh::lean_dec(v_bs_6009_);
    v_r_6011_ = leanh::lean_box((v_res_6010_) as usize);
    return v_r_6011_;
}
pub unsafe fn l_List_all___at___00List_and_spec__0(
    mut v_x_6012_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6013_: u8 = 0;
    let mut v_head_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: u8 = 0;
    let mut v_tail_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6012_) == 0 {
                    v___x_6013_ = 1;
                    return v___x_6013_;
                } else {
                    v_head_6014_ = leanh::lean_ctor_get(v_x_6012_, 0);
                    v___x_6015_ = (leanh::lean_unbox(v_head_6014_) as u8);
                    if v___x_6015_ == 0 {
                        v___x_6016_ = (leanh::lean_unbox(v_head_6014_) as u8);
                        return v___x_6016_;
                    } else {
                        v_tail_6017_ = leanh::lean_ctor_get(v_x_6012_, 1);
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
    mut v_x_6019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6020_: u8 = 0;
    let mut v_r_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6020_ = l_List_all___at___00List_and_spec__0(v_x_6019_);
    leanh::lean_dec(v_x_6019_);
    v_r_6021_ = leanh::lean_box((v_res_6020_) as usize);
    return v_r_6021_;
}
pub unsafe fn l_List_and(mut v_bs_6022_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_6023_: u8 = 0;
    v___x_6023_ = l_List_all___at___00List_and_spec__0(v_bs_6022_);
    return v___x_6023_;
}
pub unsafe fn l_List_and___boxed(
    mut v_bs_6024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6025_: u8 = 0;
    let mut v_r_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6025_ = l_List_and(v_bs_6024_);
    leanh::lean_dec(v_bs_6024_);
    v_r_6026_ = leanh::lean_box((v_res_6025_) as usize);
    return v_r_6026_;
}
pub unsafe fn l_List_zipWith___redArg(
    mut v_f_6027_: *mut leanh::LeanObject,
    mut v_x_6028_: *mut leanh::LeanObject,
    mut v_x_6029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6038_: u8 = 0;
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6028_) == 0 {
                    leanh::lean_dec(v_x_6029_);
                    leanh::lean_dec(v_f_6027_);
                    v___x_6030_ = leanh::lean_box(0);
                    return v___x_6030_;
                } else {
                    if leanh::lean_obj_tag(v_x_6029_) == 0 {
                        leanh::lean_dec_ref_known(v_x_6028_, 2);
                        leanh::lean_dec(v_f_6027_);
                        v___x_6031_ = leanh::lean_box(0);
                        return v___x_6031_;
                    } else {
                        v_head_6032_ = leanh::lean_ctor_get(v_x_6028_, 0);
                        leanh::lean_inc(v_head_6032_);
                        v_tail_6033_ = leanh::lean_ctor_get(v_x_6028_, 1);
                        leanh::lean_inc(v_tail_6033_);
                        leanh::lean_dec_ref_known(v_x_6028_, 2);
                        v_head_6034_ = leanh::lean_ctor_get(v_x_6029_, 0);
                        v_tail_6035_ = leanh::lean_ctor_get(v_x_6029_, 1);
                        v_isSharedCheck_6044_ = (!leanh::lean_is_exclusive(v_x_6029_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6037_ = v_x_6029_;
                            v_isShared_6038_ = v_isSharedCheck_6044_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_6035_);
                            leanh::lean_inc(v_head_6034_);
                            leanh::lean_dec(v_x_6029_);
                            v___x_6037_ = leanh::lean_box(0);
                            v_isShared_6038_ = v_isSharedCheck_6044_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_f_6027_);
                v___x_6039_ = leanh::lean_apply_2(v_f_6027_, v_head_6032_, v_head_6034_);
                v___x_6040_ = l_List_zipWith___redArg(v_f_6027_, v_tail_6033_, v_tail_6035_);
                if v_isShared_6038_ == 0 {
                    leanh::lean_ctor_set(v___x_6037_, 1, v___x_6040_);
                    leanh::lean_ctor_set(v___x_6037_, 0, v___x_6039_);
                    v___x_6042_ = v___x_6037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v___x_6039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 1, v___x_6040_);
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
    mut v_00_u03b1_6045_: *mut leanh::LeanObject,
    mut v_00_u03b2_6046_: *mut leanh::LeanObject,
    mut v_00_u03b3_6047_: *mut leanh::LeanObject,
    mut v_f_6048_: *mut leanh::LeanObject,
    mut v_x_6049_: *mut leanh::LeanObject,
    mut v_x_6050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6051_ = l_List_zipWith___redArg(v_f_6048_, v_x_6049_, v_x_6050_);
    return v___x_6051_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_zipWith_match__1_splitter___redArg(
    mut v_x_6052_: *mut leanh::LeanObject,
    mut v_x_6053_: *mut leanh::LeanObject,
    mut v_h__1_6054_: *mut leanh::LeanObject,
    mut v_h__2_6055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6052_) == 0 {
        let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6054_);
        v___x_6056_ = leanh::lean_apply_3(
            v_h__2_6055_,
            v_x_6052_,
            v_x_6053_,
            leanh::lean_box(0),
        );
        return v___x_6056_;
    } else {
        if leanh::lean_obj_tag(v_x_6053_) == 0 {
            let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_6054_);
            v___x_6057_ = leanh::lean_apply_3(
                v_h__2_6055_,
                v_x_6052_,
                v_x_6053_,
                leanh::lean_box(0),
            );
            return v___x_6057_;
        } else {
            let mut v_head_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_6055_);
            v_head_6058_ = leanh::lean_ctor_get(v_x_6052_, 0);
            leanh::lean_inc(v_head_6058_);
            v_tail_6059_ = leanh::lean_ctor_get(v_x_6052_, 1);
            leanh::lean_inc(v_tail_6059_);
            leanh::lean_dec_ref_known(v_x_6052_, 2);
            v_head_6060_ = leanh::lean_ctor_get(v_x_6053_, 0);
            leanh::lean_inc(v_head_6060_);
            v_tail_6061_ = leanh::lean_ctor_get(v_x_6053_, 1);
            leanh::lean_inc(v_tail_6061_);
            leanh::lean_dec_ref_known(v_x_6053_, 2);
            v___x_6062_ = leanh::lean_apply_4(
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
    mut v_00_u03b1_6063_: *mut leanh::LeanObject,
    mut v_00_u03b2_6064_: *mut leanh::LeanObject,
    mut v_motive_6065_: *mut leanh::LeanObject,
    mut v_x_6066_: *mut leanh::LeanObject,
    mut v_x_6067_: *mut leanh::LeanObject,
    mut v_h__1_6068_: *mut leanh::LeanObject,
    mut v_h__2_6069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6066_) == 0 {
        let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6068_);
        v___x_6070_ = leanh::lean_apply_3(
            v_h__2_6069_,
            v_x_6066_,
            v_x_6067_,
            leanh::lean_box(0),
        );
        return v___x_6070_;
    } else {
        if leanh::lean_obj_tag(v_x_6067_) == 0 {
            let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_6068_);
            v___x_6071_ = leanh::lean_apply_3(
                v_h__2_6069_,
                v_x_6066_,
                v_x_6067_,
                leanh::lean_box(0),
            );
            return v___x_6071_;
        } else {
            let mut v_head_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_6069_);
            v_head_6072_ = leanh::lean_ctor_get(v_x_6066_, 0);
            leanh::lean_inc(v_head_6072_);
            v_tail_6073_ = leanh::lean_ctor_get(v_x_6066_, 1);
            leanh::lean_inc(v_tail_6073_);
            leanh::lean_dec_ref_known(v_x_6066_, 2);
            v_head_6074_ = leanh::lean_ctor_get(v_x_6067_, 0);
            leanh::lean_inc(v_head_6074_);
            v_tail_6075_ = leanh::lean_ctor_get(v_x_6067_, 1);
            leanh::lean_inc(v_tail_6075_);
            leanh::lean_dec_ref_known(v_x_6067_, 2);
            v___x_6076_ = leanh::lean_apply_4(
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
    mut v_x_6077_: *mut leanh::LeanObject,
    mut v_x_6078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6085_: u8 = 0;
    let mut v_head_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6090_: u8 = 0;
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6098_: u8 = 0;
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6077_) == 0 {
                    leanh::lean_dec(v_x_6078_);
                    v___x_6079_ = leanh::lean_box(0);
                    return v___x_6079_;
                } else {
                    if leanh::lean_obj_tag(v_x_6078_) == 0 {
                        leanh::lean_dec_ref_known(v_x_6077_, 2);
                        v___x_6080_ = leanh::lean_box(0);
                        return v___x_6080_;
                    } else {
                        v_head_6081_ = leanh::lean_ctor_get(v_x_6077_, 0);
                        v_tail_6082_ = leanh::lean_ctor_get(v_x_6077_, 1);
                        v_isSharedCheck_6099_ = (!leanh::lean_is_exclusive(v_x_6077_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v___x_6084_ = v_x_6077_;
                            v_isShared_6085_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_6082_);
                            leanh::lean_inc(v_head_6081_);
                            leanh::lean_dec(v_x_6077_);
                            v___x_6084_ = leanh::lean_box(0);
                            v_isShared_6085_ = v_isSharedCheck_6099_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_head_6086_ = leanh::lean_ctor_get(v_x_6078_, 0);
                v_tail_6087_ = leanh::lean_ctor_get(v_x_6078_, 1);
                v_isSharedCheck_6098_ = (!leanh::lean_is_exclusive(v_x_6078_)) as u8;
                if v_isSharedCheck_6098_ == 0 {
                    v___x_6089_ = v_x_6078_;
                    v_isShared_6090_ = v_isSharedCheck_6098_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_6087_);
                    leanh::lean_inc(v_head_6086_);
                    leanh::lean_dec(v_x_6078_);
                    v___x_6089_ = leanh::lean_box(0);
                    v_isShared_6090_ = v_isSharedCheck_6098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6085_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6084_, 0);
                    leanh::lean_ctor_set(v___x_6084_, 1, v_head_6086_);
                    v___x_6092_ = v___x_6084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_head_6081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6097_, 1, v_head_6086_);
                    v___x_6092_ = v_reuseFailAlloc_6097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6093_ =
                    l_List_zipWith___at___00List_zip_spec__0___redArg(v_tail_6082_, v_tail_6087_);
                if v_isShared_6090_ == 0 {
                    leanh::lean_ctor_set(v___x_6089_, 1, v___x_6093_);
                    leanh::lean_ctor_set(v___x_6089_, 0, v___x_6092_);
                    v___x_6095_ = v___x_6089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6096_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6096_, 1, v___x_6093_);
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
    mut v_xs_6100_: *mut leanh::LeanObject,
    mut v_ys_6101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6102_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_6100_, v_ys_6101_);
    return v___x_6102_;
}
pub unsafe fn l_List_zip(
    mut v_00_u03b1_6103_: *mut leanh::LeanObject,
    mut v_00_u03b2_6104_: *mut leanh::LeanObject,
    mut v_xs_6105_: *mut leanh::LeanObject,
    mut v_ys_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_xs_6105_, v_ys_6106_);
    return v___x_6107_;
}
pub unsafe fn l_List_zipWith___at___00List_zip_spec__0(
    mut v_00_u03b1_6108_: *mut leanh::LeanObject,
    mut v_00_u03b2_6109_: *mut leanh::LeanObject,
    mut v_x_6110_: *mut leanh::LeanObject,
    mut v_x_6111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6112_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v_x_6110_, v_x_6111_);
    return v___x_6112_;
}
pub unsafe fn l_List_zipWithAll___redArg___lam__0(
    mut v_f_6113_: *mut leanh::LeanObject,
    mut v_b_6114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6115_ = leanh::lean_box(0);
    v___x_6116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6116_, 0, v_b_6114_);
    v___x_6117_ = leanh::lean_apply_2(v_f_6113_, v___x_6115_, v___x_6116_);
    return v___x_6117_;
}
pub unsafe fn l_List_zipWithAll___redArg___lam__1(
    mut v_f_6118_: *mut leanh::LeanObject,
    mut v_a_6119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6120_, 0, v_a_6119_);
    v___x_6121_ = leanh::lean_box(0);
    v___x_6122_ = leanh::lean_apply_2(v_f_6118_, v___x_6120_, v___x_6121_);
    return v___x_6122_;
}
pub unsafe fn l_List_zipWithAll___redArg(
    mut v_f_6123_: *mut leanh::LeanObject,
    mut v_x_6124_: *mut leanh::LeanObject,
    mut v_x_6125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6136_: u8 = 0;
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6124_) == 0 {
                    v___f_6126_ = leanh::lean_alloc_closure(
                        l_List_zipWithAll___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_6126_, 0, v_f_6123_);
                    v___x_6127_ = l_List_map___redArg(v___f_6126_, v_x_6125_);
                    return v___x_6127_;
                } else {
                    if leanh::lean_obj_tag(v_x_6125_) == 0 {
                        v___f_6128_ = leanh::lean_alloc_closure(
                            l_List_zipWithAll___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_6128_, 0, v_f_6123_);
                        v___x_6129_ = l_List_map___redArg(v___f_6128_, v_x_6124_);
                        return v___x_6129_;
                    } else {
                        v_head_6130_ = leanh::lean_ctor_get(v_x_6124_, 0);
                        leanh::lean_inc(v_head_6130_);
                        v_tail_6131_ = leanh::lean_ctor_get(v_x_6124_, 1);
                        leanh::lean_inc(v_tail_6131_);
                        leanh::lean_dec_ref_known(v_x_6124_, 2);
                        v_head_6132_ = leanh::lean_ctor_get(v_x_6125_, 0);
                        v_tail_6133_ = leanh::lean_ctor_get(v_x_6125_, 1);
                        v_isSharedCheck_6144_ = (!leanh::lean_is_exclusive(v_x_6125_)) as u8;
                        if v_isSharedCheck_6144_ == 0 {
                            v___x_6135_ = v_x_6125_;
                            v_isShared_6136_ = v_isSharedCheck_6144_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_tail_6133_);
                            leanh::lean_inc(v_head_6132_);
                            leanh::lean_dec(v_x_6125_);
                            v___x_6135_ = leanh::lean_box(0);
                            v_isShared_6136_ = v_isSharedCheck_6144_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6137_, 0, v_head_6130_);
                v___x_6138_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6138_, 0, v_head_6132_);
                leanh::lean_inc(v_f_6123_);
                v___x_6139_ = leanh::lean_apply_2(v_f_6123_, v___x_6137_, v___x_6138_);
                v___x_6140_ = l_List_zipWithAll___redArg(v_f_6123_, v_tail_6131_, v_tail_6133_);
                if v_isShared_6136_ == 0 {
                    leanh::lean_ctor_set(v___x_6135_, 1, v___x_6140_);
                    leanh::lean_ctor_set(v___x_6135_, 0, v___x_6139_);
                    v___x_6142_ = v___x_6135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6143_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 0, v___x_6139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 1, v___x_6140_);
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
    mut v_00_u03b1_6145_: *mut leanh::LeanObject,
    mut v_00_u03b2_6146_: *mut leanh::LeanObject,
    mut v_00_u03b3_6147_: *mut leanh::LeanObject,
    mut v_f_6148_: *mut leanh::LeanObject,
    mut v_x_6149_: *mut leanh::LeanObject,
    mut v_x_6150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6151_ = l_List_zipWithAll___redArg(v_f_6148_, v_x_6149_, v_x_6150_);
    return v___x_6151_;
}
pub unsafe fn l_List_unzip___redArg(
    mut v_x_6152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6158_: u8 = 0;
    let mut v_fst_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6169_: u8 = 0;
    let mut v___x_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6179_: u8 = 0;
    let mut v_isSharedCheck_6180_: u8 = 0;
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6152_) == 0 {
                    v___x_6153_ = l_List_partition___redArg___closed__0;
                    return v___x_6153_;
                } else {
                    v_head_6154_ = leanh::lean_ctor_get(v_x_6152_, 0);
                    v_tail_6155_ = leanh::lean_ctor_get(v_x_6152_, 1);
                    v_isSharedCheck_6181_ = (!leanh::lean_is_exclusive(v_x_6152_)) as u8;
                    if v_isSharedCheck_6181_ == 0 {
                        v___x_6157_ = v_x_6152_;
                        v_isShared_6158_ = v_isSharedCheck_6181_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6155_);
                        leanh::lean_inc(v_head_6154_);
                        leanh::lean_dec(v_x_6152_);
                        v___x_6157_ = leanh::lean_box(0);
                        v_isShared_6158_ = v_isSharedCheck_6181_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6159_ = leanh::lean_ctor_get(v_head_6154_, 0);
                v_snd_6160_ = leanh::lean_ctor_get(v_head_6154_, 1);
                v_isSharedCheck_6180_ = (!leanh::lean_is_exclusive(v_head_6154_)) as u8;
                if v_isSharedCheck_6180_ == 0 {
                    v___x_6162_ = v_head_6154_;
                    v_isShared_6163_ = v_isSharedCheck_6180_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6160_);
                    leanh::lean_inc(v_fst_6159_);
                    leanh::lean_dec(v_head_6154_);
                    v___x_6162_ = leanh::lean_box(0);
                    v_isShared_6163_ = v_isSharedCheck_6180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6164_ = l_List_unzip___redArg(v_tail_6155_);
                v_fst_6165_ = leanh::lean_ctor_get(v___x_6164_, 0);
                v_snd_6166_ = leanh::lean_ctor_get(v___x_6164_, 1);
                v_isSharedCheck_6179_ = (!leanh::lean_is_exclusive(v___x_6164_)) as u8;
                if v_isSharedCheck_6179_ == 0 {
                    v___x_6168_ = v___x_6164_;
                    v_isShared_6169_ = v_isSharedCheck_6179_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6166_);
                    leanh::lean_inc(v_fst_6165_);
                    leanh::lean_dec(v___x_6164_);
                    v___x_6168_ = leanh::lean_box(0);
                    v_isShared_6169_ = v_isSharedCheck_6179_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6158_ == 0 {
                    leanh::lean_ctor_set(v___x_6157_, 1, v_fst_6165_);
                    leanh::lean_ctor_set(v___x_6157_, 0, v_fst_6159_);
                    v___x_6171_ = v___x_6157_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6178_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_fst_6159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6178_, 1, v_fst_6165_);
                    v___x_6171_ = v_reuseFailAlloc_6178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6163_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6162_, 1);
                    leanh::lean_ctor_set(v___x_6162_, 1, v_snd_6166_);
                    leanh::lean_ctor_set(v___x_6162_, 0, v_snd_6160_);
                    v___x_6173_ = v___x_6162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6177_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_snd_6160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6177_, 1, v_snd_6166_);
                    v___x_6173_ = v_reuseFailAlloc_6177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6169_ == 0 {
                    leanh::lean_ctor_set(v___x_6168_, 1, v___x_6173_);
                    leanh::lean_ctor_set(v___x_6168_, 0, v___x_6171_);
                    v___x_6175_ = v___x_6168_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 0, v___x_6171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 1, v___x_6173_);
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
    mut v_00_u03b1_6182_: *mut leanh::LeanObject,
    mut v_00_u03b2_6183_: *mut leanh::LeanObject,
    mut v_x_6184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6185_ = l_List_unzip___redArg(v_x_6184_);
    return v___x_6185_;
}
pub unsafe fn l_List_sum___redArg___lam__0(
    mut v_inst_6186_: *mut leanh::LeanObject,
    mut v_x1_6187_: *mut leanh::LeanObject,
    mut v_x2_6188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6189_ = leanh::lean_apply_2(v_inst_6186_, v_x1_6187_, v_x2_6188_);
    return v___x_6189_;
}
pub unsafe fn l_List_sum___redArg(
    mut v_inst_6190_: *mut leanh::LeanObject,
    mut v_inst_6191_: *mut leanh::LeanObject,
    mut v_l_6192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6193_ = leanh::lean_alloc_closure(
        l_List_sum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6193_, 0, v_inst_6190_);
    v___x_6194_ = l_List_foldr___redArg(v___f_6193_, v_inst_6191_, v_l_6192_);
    return v___x_6194_;
}
pub unsafe fn l_List_sum___redArg___boxed(
    mut v_inst_6195_: *mut leanh::LeanObject,
    mut v_inst_6196_: *mut leanh::LeanObject,
    mut v_l_6197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6198_ = l_List_sum___redArg(v_inst_6195_, v_inst_6196_, v_l_6197_);
    leanh::lean_dec(v_inst_6196_);
    return v_res_6198_;
}
pub unsafe fn l_List_sum(
    mut v_00_u03b1_6199_: *mut leanh::LeanObject,
    mut v_inst_6200_: *mut leanh::LeanObject,
    mut v_inst_6201_: *mut leanh::LeanObject,
    mut v_l_6202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6203_ = l_List_sum___redArg(v_inst_6200_, v_inst_6201_, v_l_6202_);
    return v___x_6203_;
}
pub unsafe fn l_List_sum___boxed(
    mut v_00_u03b1_6204_: *mut leanh::LeanObject,
    mut v_inst_6205_: *mut leanh::LeanObject,
    mut v_inst_6206_: *mut leanh::LeanObject,
    mut v_l_6207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6208_ = l_List_sum(v_00_u03b1_6204_, v_inst_6205_, v_inst_6206_, v_l_6207_);
    leanh::lean_dec(v_inst_6206_);
    return v_res_6208_;
}
pub unsafe fn l_List_prod___redArg(
    mut v_inst_6209_: *mut leanh::LeanObject,
    mut v_inst_6210_: *mut leanh::LeanObject,
    mut v_l_6211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6212_ = leanh::lean_alloc_closure(
        l_List_sum___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6212_, 0, v_inst_6209_);
    v___x_6213_ = l_List_foldr___redArg(v___f_6212_, v_inst_6210_, v_l_6211_);
    return v___x_6213_;
}
pub unsafe fn l_List_prod___redArg___boxed(
    mut v_inst_6214_: *mut leanh::LeanObject,
    mut v_inst_6215_: *mut leanh::LeanObject,
    mut v_l_6216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6217_ = l_List_prod___redArg(v_inst_6214_, v_inst_6215_, v_l_6216_);
    leanh::lean_dec(v_inst_6215_);
    return v_res_6217_;
}
pub unsafe fn l_List_prod(
    mut v_00_u03b1_6218_: *mut leanh::LeanObject,
    mut v_inst_6219_: *mut leanh::LeanObject,
    mut v_inst_6220_: *mut leanh::LeanObject,
    mut v_l_6221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6222_ = l_List_prod___redArg(v_inst_6219_, v_inst_6220_, v_l_6221_);
    return v___x_6222_;
}
pub unsafe fn l_List_prod___boxed(
    mut v_00_u03b1_6223_: *mut leanh::LeanObject,
    mut v_inst_6224_: *mut leanh::LeanObject,
    mut v_inst_6225_: *mut leanh::LeanObject,
    mut v_l_6226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6227_ = l_List_prod(v_00_u03b1_6223_, v_inst_6224_, v_inst_6225_, v_l_6226_);
    leanh::lean_dec(v_inst_6225_);
    return v_res_6227_;
}
pub unsafe fn l_List_range_loop(
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6231_: u8 = 0;
    let mut v_one_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6230_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6231_ = lean_nat_dec_eq(v_a_6228_, v_zero_6230_);
                if v_isZero_6231_ == 1 {
                    leanh::lean_dec(v_a_6228_);
                    return v_a_6229_;
                } else {
                    v_one_6232_ = leanh::lean_unsigned_to_nat(1);
                    v_n_6233_ = lean_nat_sub(v_a_6228_, v_one_6232_);
                    leanh::lean_dec(v_a_6228_);
                    leanh::lean_inc(v_n_6233_);
                    v___x_6234_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6234_, 0, v_n_6233_);
                    leanh::lean_ctor_set(v___x_6234_, 1, v_a_6229_);
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
    mut v_n_6236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6237_ = leanh::lean_box(0);
    v___x_6238_ = l_List_range_loop(v_n_6236_, v___x_6237_);
    return v___x_6238_;
}
pub unsafe fn l_List_range_x27(
    mut v_x_6239_: *mut leanh::LeanObject,
    mut v_x_6240_: *mut leanh::LeanObject,
    mut v_x_6241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6243_: u8 = 0;
    v_zero_6242_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6243_ = lean_nat_dec_eq(v_x_6240_, v_zero_6242_);
    if v_isZero_6243_ == 1 {
        let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_6239_);
        v___x_6244_ = leanh::lean_box(0);
        return v___x_6244_;
    } else {
        let mut v_one_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_6245_ = leanh::lean_unsigned_to_nat(1);
        v_n_6246_ = lean_nat_sub(v_x_6240_, v_one_6245_);
        v___x_6247_ = lean_nat_add(v_x_6239_, v_x_6241_);
        v___x_6248_ = l_List_range_x27(v___x_6247_, v_n_6246_, v_x_6241_);
        leanh::lean_dec(v_n_6246_);
        v___x_6249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6249_, 0, v_x_6239_);
        leanh::lean_ctor_set(v___x_6249_, 1, v___x_6248_);
        return v___x_6249_;
    }
}
pub unsafe fn l_List_range_x27___boxed(
    mut v_x_6250_: *mut leanh::LeanObject,
    mut v_x_6251_: *mut leanh::LeanObject,
    mut v_x_6252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6253_ = l_List_range_x27(v_x_6250_, v_x_6251_, v_x_6252_);
    leanh::lean_dec(v_x_6252_);
    leanh::lean_dec(v_x_6251_);
    return v_res_6253_;
}
pub unsafe fn l_List_zipIdx___redArg(
    mut v_x_6254_: *mut leanh::LeanObject,
    mut v_x_6255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6261_: u8 = 0;
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6254_) == 0 {
                    leanh::lean_dec(v_x_6255_);
                    v___x_6256_ = leanh::lean_box(0);
                    return v___x_6256_;
                } else {
                    v_head_6257_ = leanh::lean_ctor_get(v_x_6254_, 0);
                    v_tail_6258_ = leanh::lean_ctor_get(v_x_6254_, 1);
                    v_isSharedCheck_6269_ = (!leanh::lean_is_exclusive(v_x_6254_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6260_ = v_x_6254_;
                        v_isShared_6261_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6258_);
                        leanh::lean_inc(v_head_6257_);
                        leanh::lean_dec(v_x_6254_);
                        v___x_6260_ = leanh::lean_box(0);
                        v_isShared_6261_ = v_isSharedCheck_6269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_6255_);
                v___x_6262_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6262_, 0, v_head_6257_);
                leanh::lean_ctor_set(v___x_6262_, 1, v_x_6255_);
                v___x_6263_ = leanh::lean_unsigned_to_nat(1);
                v___x_6264_ = lean_nat_add(v_x_6255_, v___x_6263_);
                leanh::lean_dec(v_x_6255_);
                v___x_6265_ = l_List_zipIdx___redArg(v_tail_6258_, v___x_6264_);
                if v_isShared_6261_ == 0 {
                    leanh::lean_ctor_set(v___x_6260_, 1, v___x_6265_);
                    leanh::lean_ctor_set(v___x_6260_, 0, v___x_6262_);
                    v___x_6267_ = v___x_6260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 1, v___x_6265_);
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
    mut v_00_u03b1_6270_: *mut leanh::LeanObject,
    mut v_x_6271_: *mut leanh::LeanObject,
    mut v_x_6272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6273_ = l_List_zipIdx___redArg(v_x_6271_, v_x_6272_);
    return v___x_6273_;
}
pub unsafe fn l_List_min_x3f___redArg(
    mut v_inst_6274_: *mut leanh::LeanObject,
    mut v_x_6275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6275_) == 0 {
        let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_6274_);
        v___x_6276_ = leanh::lean_box(0);
        return v___x_6276_;
    } else {
        let mut v_head_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_6277_ = leanh::lean_ctor_get(v_x_6275_, 0);
        leanh::lean_inc(v_head_6277_);
        v_tail_6278_ = leanh::lean_ctor_get(v_x_6275_, 1);
        leanh::lean_inc(v_tail_6278_);
        leanh::lean_dec_ref_known(v_x_6275_, 2);
        v___x_6279_ = l_List_foldl___redArg(v_inst_6274_, v_head_6277_, v_tail_6278_);
        v___x_6280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6280_, 0, v___x_6279_);
        return v___x_6280_;
    }
}
pub unsafe fn l_List_min_x3f(
    mut v_00_u03b1_6281_: *mut leanh::LeanObject,
    mut v_inst_6282_: *mut leanh::LeanObject,
    mut v_x_6283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6284_ = l_List_min_x3f___redArg(v_inst_6282_, v_x_6283_);
    return v___x_6284_;
}
pub unsafe fn l_List_min___redArg(
    mut v_inst_6285_: *mut leanh::LeanObject,
    mut v_x_6286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_6287_ = leanh::lean_ctor_get(v_x_6286_, 0);
    leanh::lean_inc(v_head_6287_);
    v_tail_6288_ = leanh::lean_ctor_get(v_x_6286_, 1);
    leanh::lean_inc(v_tail_6288_);
    leanh::lean_dec(v_x_6286_);
    v___x_6289_ = l_List_foldl___redArg(v_inst_6285_, v_head_6287_, v_tail_6288_);
    return v___x_6289_;
}
pub unsafe fn l_List_min(
    mut v_00_u03b1_6290_: *mut leanh::LeanObject,
    mut v_inst_6291_: *mut leanh::LeanObject,
    mut v_x_6292_: *mut leanh::LeanObject,
    mut v_x_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6294_ = l_List_min___redArg(v_inst_6291_, v_x_6292_);
    return v___x_6294_;
}
pub unsafe fn l_List_max_x3f___redArg(
    mut v_inst_6295_: *mut leanh::LeanObject,
    mut v_x_6296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6296_) == 0 {
        let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_6295_);
        v___x_6297_ = leanh::lean_box(0);
        return v___x_6297_;
    } else {
        let mut v_head_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_6298_ = leanh::lean_ctor_get(v_x_6296_, 0);
        leanh::lean_inc(v_head_6298_);
        v_tail_6299_ = leanh::lean_ctor_get(v_x_6296_, 1);
        leanh::lean_inc(v_tail_6299_);
        leanh::lean_dec_ref_known(v_x_6296_, 2);
        v___x_6300_ = l_List_foldl___redArg(v_inst_6295_, v_head_6298_, v_tail_6299_);
        v___x_6301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6301_, 0, v___x_6300_);
        return v___x_6301_;
    }
}
pub unsafe fn l_List_max_x3f(
    mut v_00_u03b1_6302_: *mut leanh::LeanObject,
    mut v_inst_6303_: *mut leanh::LeanObject,
    mut v_x_6304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6305_ = l_List_max_x3f___redArg(v_inst_6303_, v_x_6304_);
    return v___x_6305_;
}
pub unsafe fn l_List_max___redArg(
    mut v_inst_6306_: *mut leanh::LeanObject,
    mut v_x_6307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_6308_ = leanh::lean_ctor_get(v_x_6307_, 0);
    leanh::lean_inc(v_head_6308_);
    v_tail_6309_ = leanh::lean_ctor_get(v_x_6307_, 1);
    leanh::lean_inc(v_tail_6309_);
    leanh::lean_dec(v_x_6307_);
    v___x_6310_ = l_List_foldl___redArg(v_inst_6306_, v_head_6308_, v_tail_6309_);
    return v___x_6310_;
}
pub unsafe fn l_List_max(
    mut v_00_u03b1_6311_: *mut leanh::LeanObject,
    mut v_inst_6312_: *mut leanh::LeanObject,
    mut v_x_6313_: *mut leanh::LeanObject,
    mut v_x_6314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6315_ = l_List_max___redArg(v_inst_6312_, v_x_6313_);
    return v___x_6315_;
}
pub unsafe fn l_List_intersperse___redArg(
    mut v_sep_6316_: *mut leanh::LeanObject,
    mut v_x_6317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6328_: u8 = 0;
    let mut v_unused_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6317_) == 0 {
                    leanh::lean_dec(v_sep_6316_);
                    return v_x_6317_;
                } else {
                    v_tail_6318_ = leanh::lean_ctor_get(v_x_6317_, 1);
                    if leanh::lean_obj_tag(v_tail_6318_) == 0 {
                        leanh::lean_dec(v_sep_6316_);
                        return v_x_6317_;
                    } else {
                        leanh::lean_inc_ref(v_tail_6318_);
                        v_head_6319_ = leanh::lean_ctor_get(v_x_6317_, 0);
                        v_isSharedCheck_6328_ = (!leanh::lean_is_exclusive(v_x_6317_)) as u8;
                        if v_isSharedCheck_6328_ == 0 {
                            v_unused_6329_ = leanh::lean_ctor_get(v_x_6317_, 1);
                            leanh::lean_dec(v_unused_6329_);
                            v___x_6321_ = v_x_6317_;
                            v_isShared_6322_ = v_isSharedCheck_6328_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_6319_);
                            leanh::lean_dec(v_x_6317_);
                            v___x_6321_ = leanh::lean_box(0);
                            v_isShared_6322_ = v_isSharedCheck_6328_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_sep_6316_);
                v___x_6323_ = l_List_intersperse___redArg(v_sep_6316_, v_tail_6318_);
                if v_isShared_6322_ == 0 {
                    leanh::lean_ctor_set(v___x_6321_, 1, v___x_6323_);
                    leanh::lean_ctor_set(v___x_6321_, 0, v_sep_6316_);
                    v___x_6325_ = v___x_6321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6327_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_sep_6316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 1, v___x_6323_);
                    v___x_6325_ = v_reuseFailAlloc_6327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6326_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6326_, 0, v_head_6319_);
                leanh::lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                return v___x_6326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_intersperse(
    mut v_00_u03b1_6330_: *mut leanh::LeanObject,
    mut v_sep_6331_: *mut leanh::LeanObject,
    mut v_x_6332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6333_ = l_List_intersperse___redArg(v_sep_6331_, v_x_6332_);
    return v___x_6333_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(
    mut v___x_6334_: *mut leanh::LeanObject,
    mut v_x_6335_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6336_: u8 = 0;
    let mut v_head_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: u8 = 0;
    let mut v___x_6342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6335_) == 0 {
                    leanh::lean_dec_ref(v___x_6334_);
                    v___x_6336_ = 0;
                    return v___x_6336_;
                } else {
                    v_head_6337_ = leanh::lean_ctor_get(v_x_6335_, 0);
                    leanh::lean_inc(v_head_6337_);
                    v_tail_6338_ = leanh::lean_ctor_get(v_x_6335_, 1);
                    leanh::lean_inc(v_tail_6338_);
                    leanh::lean_dec_ref_known(v_x_6335_, 2);
                    leanh::lean_inc_ref(v___x_6334_);
                    v___x_6339_ = leanh::lean_apply_1(v___x_6334_, v_head_6337_);
                    v___x_6340_ = (leanh::lean_unbox(v___x_6339_) as u8);
                    if v___x_6340_ == 0 {
                        v_x_6335_ = v_tail_6338_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_6338_);
                        leanh::lean_dec_ref(v___x_6334_);
                        v___x_6342_ = (leanh::lean_unbox(v___x_6339_) as u8);
                        return v___x_6342_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg___boxed(
    mut v___x_6343_: *mut leanh::LeanObject,
    mut v_x_6344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6345_: u8 = 0;
    let mut v_r_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6345_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_6343_, v_x_6344_);
    v_r_6346_ = leanh::lean_box((v_res_6345_) as usize);
    return v_r_6346_;
}
pub unsafe fn l_List_eraseDupsBy_loop___redArg(
    mut v_r_6347_: *mut leanh::LeanObject,
    mut v_a_6348_: *mut leanh::LeanObject,
    mut v_a_6349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6355_: u8 = 0;
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: u8 = 0;
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6348_) == 0 {
                    leanh::lean_dec_ref(v_r_6347_);
                    v___x_6350_ = l_List_reverse___redArg(v_a_6349_);
                    return v___x_6350_;
                } else {
                    v_head_6351_ = leanh::lean_ctor_get(v_a_6348_, 0);
                    v_tail_6352_ = leanh::lean_ctor_get(v_a_6348_, 1);
                    v_isSharedCheck_6363_ = (!leanh::lean_is_exclusive(v_a_6348_)) as u8;
                    if v_isSharedCheck_6363_ == 0 {
                        v___x_6354_ = v_a_6348_;
                        v_isShared_6355_ = v_isSharedCheck_6363_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6352_);
                        leanh::lean_inc(v_head_6351_);
                        leanh::lean_dec(v_a_6348_);
                        v___x_6354_ = leanh::lean_box(0);
                        v_isShared_6355_ = v_isSharedCheck_6363_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_r_6347_);
                leanh::lean_inc(v_head_6351_);
                v___x_6356_ = leanh::lean_apply_1(v_r_6347_, v_head_6351_);
                leanh::lean_inc(v_a_6349_);
                v___x_6357_ = l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(
                    v___x_6356_,
                    v_a_6349_,
                );
                if v___x_6357_ == 0 {
                    if v_isShared_6355_ == 0 {
                        leanh::lean_ctor_set(v___x_6354_, 1, v_a_6349_);
                        v___x_6359_ = v___x_6354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6361_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_head_6351_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6361_, 1, v_a_6349_);
                        v___x_6359_ = v_reuseFailAlloc_6361_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6354_);
                    leanh::lean_dec(v_head_6351_);
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
    mut v_00_u03b1_6364_: *mut leanh::LeanObject,
    mut v_r_6365_: *mut leanh::LeanObject,
    mut v_a_6366_: *mut leanh::LeanObject,
    mut v_a_6367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6368_ = l_List_eraseDupsBy_loop___redArg(v_r_6365_, v_a_6366_, v_a_6367_);
    return v___x_6368_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0(
    mut v_00_u03b1_6369_: *mut leanh::LeanObject,
    mut v___x_6370_: *mut leanh::LeanObject,
    mut v_x_6371_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6372_: u8 = 0;
    v___x_6372_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0___redArg(v___x_6370_, v_x_6371_);
    return v___x_6372_;
}
pub unsafe fn l_List_any___at___00List_eraseDupsBy_loop_spec__0___boxed(
    mut v_00_u03b1_6373_: *mut leanh::LeanObject,
    mut v___x_6374_: *mut leanh::LeanObject,
    mut v_x_6375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6376_: u8 = 0;
    let mut v_r_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6376_ =
        l_List_any___at___00List_eraseDupsBy_loop_spec__0(v_00_u03b1_6373_, v___x_6374_, v_x_6375_);
    v_r_6377_ = leanh::lean_box((v_res_6376_) as usize);
    return v_r_6377_;
}
pub unsafe fn l_List_eraseDupsBy___redArg(
    mut v_r_6378_: *mut leanh::LeanObject,
    mut v_as_6379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6380_ = leanh::lean_box(0);
    v___x_6381_ = l_List_eraseDupsBy_loop___redArg(v_r_6378_, v_as_6379_, v___x_6380_);
    return v___x_6381_;
}
pub unsafe fn l_List_eraseDupsBy(
    mut v_00_u03b1_6382_: *mut leanh::LeanObject,
    mut v_r_6383_: *mut leanh::LeanObject,
    mut v_as_6384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6385_ = l_List_eraseDupsBy___redArg(v_r_6383_, v_as_6384_);
    return v___x_6385_;
}
pub unsafe fn l_List_eraseDups___redArg___lam__0(
    mut v_inst_6386_: *mut leanh::LeanObject,
    mut v_x1_6387_: *mut leanh::LeanObject,
    mut v_x2_6388_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: u8 = 0;
    v___x_6389_ = leanh::lean_apply_2(v_inst_6386_, v_x1_6387_, v_x2_6388_);
    v___x_6390_ = (leanh::lean_unbox(v___x_6389_) as u8);
    return v___x_6390_;
}
pub unsafe fn l_List_eraseDups___redArg___lam__0___boxed(
    mut v_inst_6391_: *mut leanh::LeanObject,
    mut v_x1_6392_: *mut leanh::LeanObject,
    mut v_x2_6393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6394_: u8 = 0;
    let mut v_r_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_List_eraseDups___redArg___lam__0(v_inst_6391_, v_x1_6392_, v_x2_6393_);
    v_r_6395_ = leanh::lean_box((v_res_6394_) as usize);
    return v_r_6395_;
}
pub unsafe fn l_List_eraseDups___redArg(
    mut v_inst_6396_: *mut leanh::LeanObject,
    mut v_as_6397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6398_ = leanh::lean_alloc_closure(
        l_List_eraseDups___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6398_, 0, v_inst_6396_);
    v___x_6399_ = l_List_eraseDupsBy___redArg(v___f_6398_, v_as_6397_);
    return v___x_6399_;
}
pub unsafe fn l_List_eraseDups(
    mut v_00_u03b1_6400_: *mut leanh::LeanObject,
    mut v_inst_6401_: *mut leanh::LeanObject,
    mut v_as_6402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6403_ = l_List_eraseDups___redArg(v_inst_6401_, v_as_6402_);
    return v___x_6403_;
}
pub unsafe fn l_List_eraseRepsBy_loop___redArg(
    mut v_r_6404_: *mut leanh::LeanObject,
    mut v_a_6405_: *mut leanh::LeanObject,
    mut v_a_6406_: *mut leanh::LeanObject,
    mut v_a_6407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: u8 = 0;
    let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6406_) == 0 {
                    leanh::lean_dec_ref(v_r_6404_);
                    v___x_6408_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6408_, 0, v_a_6405_);
                    leanh::lean_ctor_set(v___x_6408_, 1, v_a_6407_);
                    v___x_6409_ = l_List_reverse___redArg(v___x_6408_);
                    return v___x_6409_;
                } else {
                    v_head_6410_ = leanh::lean_ctor_get(v_a_6406_, 0);
                    v_tail_6411_ = leanh::lean_ctor_get(v_a_6406_, 1);
                    v_isSharedCheck_6422_ = (!leanh::lean_is_exclusive(v_a_6406_)) as u8;
                    if v_isSharedCheck_6422_ == 0 {
                        v___x_6413_ = v_a_6406_;
                        v_isShared_6414_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6411_);
                        leanh::lean_inc(v_head_6410_);
                        leanh::lean_dec(v_a_6406_);
                        v___x_6413_ = leanh::lean_box(0);
                        v_isShared_6414_ = v_isSharedCheck_6422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_r_6404_);
                leanh::lean_inc(v_head_6410_);
                leanh::lean_inc(v_a_6405_);
                v___x_6415_ = leanh::lean_apply_2(v_r_6404_, v_a_6405_, v_head_6410_);
                v___x_6416_ = (leanh::lean_unbox(v___x_6415_) as u8);
                if v___x_6416_ == 0 {
                    if v_isShared_6414_ == 0 {
                        leanh::lean_ctor_set(v___x_6413_, 1, v_a_6407_);
                        leanh::lean_ctor_set(v___x_6413_, 0, v_a_6405_);
                        v___x_6418_ = v___x_6413_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6420_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6405_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6420_, 1, v_a_6407_);
                        v___x_6418_ = v_reuseFailAlloc_6420_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6413_);
                    leanh::lean_dec(v_head_6410_);
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
    mut v_00_u03b1_6423_: *mut leanh::LeanObject,
    mut v_r_6424_: *mut leanh::LeanObject,
    mut v_a_6425_: *mut leanh::LeanObject,
    mut v_a_6426_: *mut leanh::LeanObject,
    mut v_a_6427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l_List_eraseRepsBy_loop___redArg(v_r_6424_, v_a_6425_, v_a_6426_, v_a_6427_);
    return v___x_6428_;
}
pub unsafe fn l_List_eraseRepsBy___redArg(
    mut v_r_6429_: *mut leanh::LeanObject,
    mut v_x_6430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6430_) == 0 {
        leanh::lean_dec_ref(v_r_6429_);
        return v_x_6430_;
    } else {
        let mut v_head_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_6431_ = leanh::lean_ctor_get(v_x_6430_, 0);
        leanh::lean_inc(v_head_6431_);
        v_tail_6432_ = leanh::lean_ctor_get(v_x_6430_, 1);
        leanh::lean_inc(v_tail_6432_);
        leanh::lean_dec_ref_known(v_x_6430_, 2);
        v___x_6433_ = leanh::lean_box(0);
        v___x_6434_ =
            l_List_eraseRepsBy_loop___redArg(v_r_6429_, v_head_6431_, v_tail_6432_, v___x_6433_);
        return v___x_6434_;
    }
}
pub unsafe fn l_List_eraseRepsBy(
    mut v_00_u03b1_6435_: *mut leanh::LeanObject,
    mut v_r_6436_: *mut leanh::LeanObject,
    mut v_x_6437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6438_ = l_List_eraseRepsBy___redArg(v_r_6436_, v_x_6437_);
    return v___x_6438_;
}
pub unsafe fn l_List_eraseReps___redArg(
    mut v_inst_6439_: *mut leanh::LeanObject,
    mut v_as_6440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6441_ = leanh::lean_alloc_closure(
        l_List_eraseDups___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_6441_, 0, v_inst_6439_);
    v___x_6442_ = l_List_eraseRepsBy___redArg(v___f_6441_, v_as_6440_);
    return v___x_6442_;
}
pub unsafe fn l_List_eraseReps(
    mut v_00_u03b1_6443_: *mut leanh::LeanObject,
    mut v_inst_6444_: *mut leanh::LeanObject,
    mut v_as_6445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6446_ = l_List_eraseReps___redArg(v_inst_6444_, v_as_6445_);
    return v___x_6446_;
}
pub unsafe fn l_List_span_loop___redArg(
    mut v_p_6447_: *mut leanh::LeanObject,
    mut v_a_6448_: *mut leanh::LeanObject,
    mut v_a_6449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: u8 = 0;
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6465_: u8 = 0;
    let mut v_unused_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6448_) == 0 {
                    leanh::lean_dec_ref(v_p_6447_);
                    v___x_6450_ = l_List_reverse___redArg(v_a_6449_);
                    v___x_6451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6451_, 0, v___x_6450_);
                    leanh::lean_ctor_set(v___x_6451_, 1, v_a_6448_);
                    return v___x_6451_;
                } else {
                    v_head_6452_ = leanh::lean_ctor_get(v_a_6448_, 0);
                    v_tail_6453_ = leanh::lean_ctor_get(v_a_6448_, 1);
                    leanh::lean_inc_ref(v_p_6447_);
                    leanh::lean_inc(v_head_6452_);
                    v___x_6454_ = leanh::lean_apply_1(v_p_6447_, v_head_6452_);
                    v___x_6455_ = (leanh::lean_unbox(v___x_6454_) as u8);
                    if v___x_6455_ == 0 {
                        leanh::lean_dec_ref(v_p_6447_);
                        v___x_6456_ = l_List_reverse___redArg(v_a_6449_);
                        v___x_6457_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6457_, 0, v___x_6456_);
                        leanh::lean_ctor_set(v___x_6457_, 1, v_a_6448_);
                        return v___x_6457_;
                    } else {
                        leanh::lean_inc(v_tail_6453_);
                        leanh::lean_inc(v_head_6452_);
                        v_isSharedCheck_6465_ = (!leanh::lean_is_exclusive(v_a_6448_)) as u8;
                        if v_isSharedCheck_6465_ == 0 {
                            v_unused_6466_ = leanh::lean_ctor_get(v_a_6448_, 1);
                            leanh::lean_dec(v_unused_6466_);
                            v_unused_6467_ = leanh::lean_ctor_get(v_a_6448_, 0);
                            leanh::lean_dec(v_unused_6467_);
                            v___x_6459_ = v_a_6448_;
                            v_isShared_6460_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_6448_);
                            v___x_6459_ = leanh::lean_box(0);
                            v_isShared_6460_ = v_isSharedCheck_6465_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6460_ == 0 {
                    leanh::lean_ctor_set(v___x_6459_, 1, v_a_6449_);
                    v___x_6462_ = v___x_6459_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6464_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_head_6452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6464_, 1, v_a_6449_);
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
    mut v_00_u03b1_6468_: *mut leanh::LeanObject,
    mut v_p_6469_: *mut leanh::LeanObject,
    mut v_a_6470_: *mut leanh::LeanObject,
    mut v_a_6471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6472_ = l_List_span_loop___redArg(v_p_6469_, v_a_6470_, v_a_6471_);
    return v___x_6472_;
}
pub unsafe fn l_List_span___redArg(
    mut v_p_6473_: *mut leanh::LeanObject,
    mut v_as_6474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6475_ = leanh::lean_box(0);
    v___x_6476_ = l_List_span_loop___redArg(v_p_6473_, v_as_6474_, v___x_6475_);
    return v___x_6476_;
}
pub unsafe fn l_List_span(
    mut v_00_u03b1_6477_: *mut leanh::LeanObject,
    mut v_p_6478_: *mut leanh::LeanObject,
    mut v_as_6479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = leanh::lean_box(0);
    v___x_6481_ = l_List_span_loop___redArg(v_p_6478_, v_as_6479_, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn l_List_splitBy_loop___redArg(
    mut v_R_6482_: *mut leanh::LeanObject,
    mut v_a_6483_: *mut leanh::LeanObject,
    mut v_a_6484_: *mut leanh::LeanObject,
    mut v_a_6485_: *mut leanh::LeanObject,
    mut v_a_6486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6495_: u8 = 0;
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: u8 = 0;
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6483_) == 0 {
                    leanh::lean_dec_ref(v_R_6482_);
                    v___x_6487_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6487_, 0, v_a_6484_);
                    leanh::lean_ctor_set(v___x_6487_, 1, v_a_6485_);
                    v___x_6488_ = l_List_reverse___redArg(v___x_6487_);
                    v___x_6489_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6489_, 0, v___x_6488_);
                    leanh::lean_ctor_set(v___x_6489_, 1, v_a_6486_);
                    v___x_6490_ = l_List_reverse___redArg(v___x_6489_);
                    return v___x_6490_;
                } else {
                    v_head_6491_ = leanh::lean_ctor_get(v_a_6483_, 0);
                    v_tail_6492_ = leanh::lean_ctor_get(v_a_6483_, 1);
                    v_isSharedCheck_6509_ = (!leanh::lean_is_exclusive(v_a_6483_)) as u8;
                    if v_isSharedCheck_6509_ == 0 {
                        v___x_6494_ = v_a_6483_;
                        v_isShared_6495_ = v_isSharedCheck_6509_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6492_);
                        leanh::lean_inc(v_head_6491_);
                        leanh::lean_dec(v_a_6483_);
                        v___x_6494_ = leanh::lean_box(0);
                        v_isShared_6495_ = v_isSharedCheck_6509_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_R_6482_);
                leanh::lean_inc(v_head_6491_);
                leanh::lean_inc(v_a_6484_);
                v___x_6496_ = leanh::lean_apply_2(v_R_6482_, v_a_6484_, v_head_6491_);
                v___x_6497_ = (leanh::lean_unbox(v___x_6496_) as u8);
                if v___x_6497_ == 0 {
                    v___x_6498_ = leanh::lean_box(0);
                    if v_isShared_6495_ == 0 {
                        leanh::lean_ctor_set(v___x_6494_, 1, v_a_6485_);
                        leanh::lean_ctor_set(v___x_6494_, 0, v_a_6484_);
                        v___x_6500_ = v___x_6494_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6504_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6484_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 1, v_a_6485_);
                        v___x_6500_ = v_reuseFailAlloc_6504_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_6495_ == 0 {
                        leanh::lean_ctor_set(v___x_6494_, 1, v_a_6485_);
                        leanh::lean_ctor_set(v___x_6494_, 0, v_a_6484_);
                        v___x_6506_ = v___x_6494_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6508_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 0, v_a_6484_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 1, v_a_6485_);
                        v___x_6506_ = v_reuseFailAlloc_6508_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6501_ = l_List_reverse___redArg(v___x_6500_);
                v___x_6502_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6502_, 0, v___x_6501_);
                leanh::lean_ctor_set(v___x_6502_, 1, v_a_6486_);
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
    mut v_00_u03b1_6510_: *mut leanh::LeanObject,
    mut v_R_6511_: *mut leanh::LeanObject,
    mut v_a_6512_: *mut leanh::LeanObject,
    mut v_a_6513_: *mut leanh::LeanObject,
    mut v_a_6514_: *mut leanh::LeanObject,
    mut v_a_6515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6516_ =
        l_List_splitBy_loop___redArg(v_R_6511_, v_a_6512_, v_a_6513_, v_a_6514_, v_a_6515_);
    return v___x_6516_;
}
pub unsafe fn l_List_splitBy___redArg(
    mut v_R_6517_: *mut leanh::LeanObject,
    mut v_x_6518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6518_) == 0 {
        let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_R_6517_);
        v___x_6519_ = leanh::lean_box(0);
        return v___x_6519_;
    } else {
        let mut v_head_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_6520_ = leanh::lean_ctor_get(v_x_6518_, 0);
        leanh::lean_inc(v_head_6520_);
        v_tail_6521_ = leanh::lean_ctor_get(v_x_6518_, 1);
        leanh::lean_inc(v_tail_6521_);
        leanh::lean_dec_ref_known(v_x_6518_, 2);
        v___x_6522_ = leanh::lean_box(0);
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
    mut v_00_u03b1_6524_: *mut leanh::LeanObject,
    mut v_R_6525_: *mut leanh::LeanObject,
    mut v_x_6526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6527_ = l_List_splitBy___redArg(v_R_6525_, v_x_6526_);
    return v___x_6527_;
}
pub unsafe fn l_List_removeAll___redArg___lam__0(
    mut v_inst_6528_: *mut leanh::LeanObject,
    mut v_ys_6529_: *mut leanh::LeanObject,
    mut v_x_6530_: *mut leanh::LeanObject,
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
    mut v_inst_6534_: *mut leanh::LeanObject,
    mut v_ys_6535_: *mut leanh::LeanObject,
    mut v_x_6536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6537_: u8 = 0;
    let mut v_r_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6537_ = l_List_removeAll___redArg___lam__0(v_inst_6534_, v_ys_6535_, v_x_6536_);
    v_r_6538_ = leanh::lean_box((v_res_6537_) as usize);
    return v_r_6538_;
}
pub unsafe fn l_List_removeAll___redArg(
    mut v_inst_6539_: *mut leanh::LeanObject,
    mut v_xs_6540_: *mut leanh::LeanObject,
    mut v_ys_6541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6542_ = leanh::lean_alloc_closure(
        l_List_removeAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_6542_, 0, v_inst_6539_);
    leanh::lean_closure_set(v___f_6542_, 1, v_ys_6541_);
    v___x_6543_ = l_List_filter___redArg(v___f_6542_, v_xs_6540_);
    return v___x_6543_;
}
pub unsafe fn l_List_removeAll(
    mut v_00_u03b1_6544_: *mut leanh::LeanObject,
    mut v_inst_6545_: *mut leanh::LeanObject,
    mut v_xs_6546_: *mut leanh::LeanObject,
    mut v_ys_6547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6548_ = l_List_removeAll___redArg(v_inst_6545_, v_xs_6546_, v_ys_6547_);
    return v___x_6548_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter___redArg(
    mut v_ys_6549_: *mut leanh::LeanObject,
    mut v_h__1_6550_: *mut leanh::LeanObject,
    mut v_h__2_6551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_ys_6549_) == 0 {
        let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6551_);
        v___x_6552_ = leanh::lean_box(0);
        v___x_6553_ = leanh::lean_apply_1(v_h__1_6550_, v___x_6552_);
        return v___x_6553_;
    } else {
        let mut v_head_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6550_);
        v_head_6554_ = leanh::lean_ctor_get(v_ys_6549_, 0);
        leanh::lean_inc(v_head_6554_);
        v_tail_6555_ = leanh::lean_ctor_get(v_ys_6549_, 1);
        leanh::lean_inc(v_tail_6555_);
        leanh::lean_dec_ref_known(v_ys_6549_, 2);
        v___x_6556_ = leanh::lean_apply_2(v_h__2_6551_, v_head_6554_, v_tail_6555_);
        return v___x_6556_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__instDecidableEqList_match__1_splitter(
    mut v_00_u03b1_6557_: *mut leanh::LeanObject,
    mut v_motive_6558_: *mut leanh::LeanObject,
    mut v_ys_6559_: *mut leanh::LeanObject,
    mut v_h__1_6560_: *mut leanh::LeanObject,
    mut v_h__2_6561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_ys_6559_) == 0 {
        let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6561_);
        v___x_6562_ = leanh::lean_box(0);
        v___x_6563_ = leanh::lean_apply_1(v_h__1_6560_, v___x_6562_);
        return v___x_6563_;
    } else {
        let mut v_head_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6560_);
        v_head_6564_ = leanh::lean_ctor_get(v_ys_6559_, 0);
        leanh::lean_inc(v_head_6564_);
        v_tail_6565_ = leanh::lean_ctor_get(v_ys_6559_, 1);
        leanh::lean_inc(v_tail_6565_);
        leanh::lean_dec_ref_known(v_ys_6559_, 2);
        v___x_6566_ = leanh::lean_apply_2(v_h__2_6561_, v_head_6564_, v_tail_6565_);
        return v___x_6566_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter___redArg(
    mut v_x_6567_: *mut leanh::LeanObject,
    mut v_x_6568_: *mut leanh::LeanObject,
    mut v_h__1_6569_: *mut leanh::LeanObject,
    mut v_h__2_6570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6567_) == 0 {
        let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6570_);
        v___x_6571_ = leanh::lean_apply_1(v_h__1_6569_, v_x_6568_);
        return v___x_6571_;
    } else {
        let mut v_head_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6569_);
        v_head_6572_ = leanh::lean_ctor_get(v_x_6567_, 0);
        leanh::lean_inc(v_head_6572_);
        v_tail_6573_ = leanh::lean_ctor_get(v_x_6567_, 1);
        leanh::lean_inc(v_tail_6573_);
        leanh::lean_dec_ref_known(v_x_6567_, 2);
        v___x_6574_ =
            leanh::lean_apply_3(v_h__2_6570_, v_head_6572_, v_tail_6573_, v_x_6568_);
        return v___x_6574_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_lengthTRAux_match__1_splitter(
    mut v_00_u03b1_6575_: *mut leanh::LeanObject,
    mut v_motive_6576_: *mut leanh::LeanObject,
    mut v_x_6577_: *mut leanh::LeanObject,
    mut v_x_6578_: *mut leanh::LeanObject,
    mut v_h__1_6579_: *mut leanh::LeanObject,
    mut v_h__2_6580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6577_) == 0 {
        let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6580_);
        v___x_6581_ = leanh::lean_apply_1(v_h__1_6579_, v_x_6578_);
        return v___x_6581_;
    } else {
        let mut v_head_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6579_);
        v_head_6582_ = leanh::lean_ctor_get(v_x_6577_, 0);
        leanh::lean_inc(v_head_6582_);
        v_tail_6583_ = leanh::lean_ctor_get(v_x_6577_, 1);
        leanh::lean_inc(v_tail_6583_);
        leanh::lean_dec_ref_known(v_x_6577_, 2);
        v___x_6584_ =
            leanh::lean_apply_3(v_h__2_6580_, v_head_6582_, v_tail_6583_, v_x_6578_);
        return v___x_6584_;
    }
}
pub unsafe fn l_List_mapTR_loop___redArg(
    mut v_f_6585_: *mut leanh::LeanObject,
    mut v_a_6586_: *mut leanh::LeanObject,
    mut v_a_6587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6593_: u8 = 0;
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6586_) == 0 {
                    leanh::lean_dec(v_f_6585_);
                    v___x_6588_ = l_List_reverse___redArg(v_a_6587_);
                    return v___x_6588_;
                } else {
                    v_head_6589_ = leanh::lean_ctor_get(v_a_6586_, 0);
                    v_tail_6590_ = leanh::lean_ctor_get(v_a_6586_, 1);
                    v_isSharedCheck_6599_ = (!leanh::lean_is_exclusive(v_a_6586_)) as u8;
                    if v_isSharedCheck_6599_ == 0 {
                        v___x_6592_ = v_a_6586_;
                        v_isShared_6593_ = v_isSharedCheck_6599_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6590_);
                        leanh::lean_inc(v_head_6589_);
                        leanh::lean_dec(v_a_6586_);
                        v___x_6592_ = leanh::lean_box(0);
                        v_isShared_6593_ = v_isSharedCheck_6599_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_f_6585_);
                v___x_6594_ = leanh::lean_apply_1(v_f_6585_, v_head_6589_);
                if v_isShared_6593_ == 0 {
                    leanh::lean_ctor_set(v___x_6592_, 1, v_a_6587_);
                    leanh::lean_ctor_set(v___x_6592_, 0, v___x_6594_);
                    v___x_6596_ = v___x_6592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 1, v_a_6587_);
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
    mut v_00_u03b1_6600_: *mut leanh::LeanObject,
    mut v_00_u03b2_6601_: *mut leanh::LeanObject,
    mut v_f_6602_: *mut leanh::LeanObject,
    mut v_a_6603_: *mut leanh::LeanObject,
    mut v_a_6604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = l_List_mapTR_loop___redArg(v_f_6602_, v_a_6603_, v_a_6604_);
    return v___x_6605_;
}
pub unsafe fn l_List_mapTR___redArg(
    mut v_f_6606_: *mut leanh::LeanObject,
    mut v_as_6607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6608_ = leanh::lean_box(0);
    v___x_6609_ = l_List_mapTR_loop___redArg(v_f_6606_, v_as_6607_, v___x_6608_);
    return v___x_6609_;
}
pub unsafe fn l_List_mapTR(
    mut v_00_u03b1_6610_: *mut leanh::LeanObject,
    mut v_00_u03b2_6611_: *mut leanh::LeanObject,
    mut v_f_6612_: *mut leanh::LeanObject,
    mut v_as_6613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6614_ = leanh::lean_box(0);
    v___x_6615_ = l_List_mapTR_loop___redArg(v_f_6612_, v_as_6613_, v___x_6614_);
    return v___x_6615_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter___redArg(
    mut v_x_6616_: *mut leanh::LeanObject,
    mut v_x_6617_: *mut leanh::LeanObject,
    mut v_h__1_6618_: *mut leanh::LeanObject,
    mut v_h__2_6619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6616_) == 0 {
        let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6619_);
        v___x_6620_ = leanh::lean_apply_1(v_h__1_6618_, v_x_6617_);
        return v___x_6620_;
    } else {
        let mut v_head_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6618_);
        v_head_6621_ = leanh::lean_ctor_get(v_x_6616_, 0);
        leanh::lean_inc(v_head_6621_);
        v_tail_6622_ = leanh::lean_ctor_get(v_x_6616_, 1);
        leanh::lean_inc(v_tail_6622_);
        leanh::lean_dec_ref_known(v_x_6616_, 2);
        v___x_6623_ =
            leanh::lean_apply_3(v_h__2_6619_, v_head_6621_, v_tail_6622_, v_x_6617_);
        return v___x_6623_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_mapTR_loop_match__1_splitter(
    mut v_00_u03b1_6624_: *mut leanh::LeanObject,
    mut v_00_u03b2_6625_: *mut leanh::LeanObject,
    mut v_motive_6626_: *mut leanh::LeanObject,
    mut v_x_6627_: *mut leanh::LeanObject,
    mut v_x_6628_: *mut leanh::LeanObject,
    mut v_h__1_6629_: *mut leanh::LeanObject,
    mut v_h__2_6630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6627_) == 0 {
        let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6630_);
        v___x_6631_ = leanh::lean_apply_1(v_h__1_6629_, v_x_6628_);
        return v___x_6631_;
    } else {
        let mut v_head_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6629_);
        v_head_6632_ = leanh::lean_ctor_get(v_x_6627_, 0);
        leanh::lean_inc(v_head_6632_);
        v_tail_6633_ = leanh::lean_ctor_get(v_x_6627_, 1);
        leanh::lean_inc(v_tail_6633_);
        leanh::lean_dec_ref_known(v_x_6627_, 2);
        v___x_6634_ =
            leanh::lean_apply_3(v_h__2_6630_, v_head_6632_, v_tail_6633_, v_x_6628_);
        return v___x_6634_;
    }
}
pub unsafe fn l_List_filterTR_loop___redArg(
    mut v_p_6635_: *mut leanh::LeanObject,
    mut v_a_6636_: *mut leanh::LeanObject,
    mut v_a_6637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6643_: u8 = 0;
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: u8 = 0;
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6636_) == 0 {
                    leanh::lean_dec_ref(v_p_6635_);
                    v___x_6638_ = l_List_reverse___redArg(v_a_6637_);
                    return v___x_6638_;
                } else {
                    v_head_6639_ = leanh::lean_ctor_get(v_a_6636_, 0);
                    v_tail_6640_ = leanh::lean_ctor_get(v_a_6636_, 1);
                    v_isSharedCheck_6651_ = (!leanh::lean_is_exclusive(v_a_6636_)) as u8;
                    if v_isSharedCheck_6651_ == 0 {
                        v___x_6642_ = v_a_6636_;
                        v_isShared_6643_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6640_);
                        leanh::lean_inc(v_head_6639_);
                        leanh::lean_dec(v_a_6636_);
                        v___x_6642_ = leanh::lean_box(0);
                        v_isShared_6643_ = v_isSharedCheck_6651_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_p_6635_);
                leanh::lean_inc(v_head_6639_);
                v___x_6644_ = leanh::lean_apply_1(v_p_6635_, v_head_6639_);
                v___x_6645_ = (leanh::lean_unbox(v___x_6644_) as u8);
                if v___x_6645_ == 0 {
                    leanh::lean_del_object(v___x_6642_);
                    leanh::lean_dec(v_head_6639_);
                    v_a_6636_ = v_tail_6640_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_6643_ == 0 {
                        leanh::lean_ctor_set(v___x_6642_, 1, v_a_6637_);
                        v___x_6648_ = v___x_6642_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6650_, 0, v_head_6639_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6650_, 1, v_a_6637_);
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
    mut v_00_u03b1_6652_: *mut leanh::LeanObject,
    mut v_p_6653_: *mut leanh::LeanObject,
    mut v_a_6654_: *mut leanh::LeanObject,
    mut v_a_6655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6656_ = l_List_filterTR_loop___redArg(v_p_6653_, v_a_6654_, v_a_6655_);
    return v___x_6656_;
}
pub unsafe fn l_List_filterTR___redArg(
    mut v_p_6657_: *mut leanh::LeanObject,
    mut v_as_6658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6659_ = leanh::lean_box(0);
    v___x_6660_ = l_List_filterTR_loop___redArg(v_p_6657_, v_as_6658_, v___x_6659_);
    return v___x_6660_;
}
pub unsafe fn l_List_filterTR(
    mut v_00_u03b1_6661_: *mut leanh::LeanObject,
    mut v_p_6662_: *mut leanh::LeanObject,
    mut v_as_6663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6664_ = leanh::lean_box(0);
    v___x_6665_ = l_List_filterTR_loop___redArg(v_p_6662_, v_as_6663_, v___x_6664_);
    return v___x_6665_;
}
pub unsafe fn l_List_replicateTR_loop___redArg(
    mut v_a_6666_: *mut leanh::LeanObject,
    mut v_a_6667_: *mut leanh::LeanObject,
    mut v_a_6668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6670_: u8 = 0;
    let mut v_one_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6669_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6670_ = lean_nat_dec_eq(v_a_6667_, v_zero_6669_);
                if v_isZero_6670_ == 1 {
                    leanh::lean_dec(v_a_6667_);
                    leanh::lean_dec(v_a_6666_);
                    return v_a_6668_;
                } else {
                    v_one_6671_ = leanh::lean_unsigned_to_nat(1);
                    v_n_6672_ = lean_nat_sub(v_a_6667_, v_one_6671_);
                    leanh::lean_dec(v_a_6667_);
                    leanh::lean_inc(v_a_6666_);
                    v___x_6673_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6673_, 0, v_a_6666_);
                    leanh::lean_ctor_set(v___x_6673_, 1, v_a_6668_);
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
    mut v_00_u03b1_6675_: *mut leanh::LeanObject,
    mut v_a_6676_: *mut leanh::LeanObject,
    mut v_a_6677_: *mut leanh::LeanObject,
    mut v_a_6678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6679_ = l_List_replicateTR_loop___redArg(v_a_6676_, v_a_6677_, v_a_6678_);
    return v___x_6679_;
}
pub unsafe fn l_List_replicateTR___redArg(
    mut v_n_6680_: *mut leanh::LeanObject,
    mut v_a_6681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6682_ = leanh::lean_box(0);
    v___x_6683_ = l_List_replicateTR_loop___redArg(v_a_6681_, v_n_6680_, v___x_6682_);
    return v___x_6683_;
}
pub unsafe fn l_List_replicateTR(
    mut v_00_u03b1_6684_: *mut leanh::LeanObject,
    mut v_n_6685_: *mut leanh::LeanObject,
    mut v_a_6686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6687_ = l_List_replicateTR___redArg(v_n_6685_, v_a_6686_);
    return v___x_6687_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(
    mut v_x_6688_: *mut leanh::LeanObject,
    mut v_x_6689_: *mut leanh::LeanObject,
    mut v_h__1_6690_: *mut leanh::LeanObject,
    mut v_h__2_6691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6693_: u8 = 0;
    v_zero_6692_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6693_ = lean_nat_dec_eq(v_x_6688_, v_zero_6692_);
    if v_isZero_6693_ == 1 {
        let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6691_);
        v___x_6694_ = leanh::lean_apply_1(v_h__1_6690_, v_x_6689_);
        return v___x_6694_;
    } else {
        let mut v_one_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6690_);
        v_one_6695_ = leanh::lean_unsigned_to_nat(1);
        v_n_6696_ = lean_nat_sub(v_x_6688_, v_one_6695_);
        v___x_6697_ = leanh::lean_apply_2(v_h__2_6691_, v_n_6696_, v_x_6689_);
        return v___x_6697_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg___boxed(
    mut v_x_6698_: *mut leanh::LeanObject,
    mut v_x_6699_: *mut leanh::LeanObject,
    mut v_h__1_6700_: *mut leanh::LeanObject,
    mut v_h__2_6701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6702_ =
        l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___redArg(
            v_x_6698_,
            v_x_6699_,
            v_h__1_6700_,
            v_h__2_6701_,
        );
    leanh::lean_dec(v_x_6698_);
    return v_res_6702_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(
    mut v_00_u03b1_6703_: *mut leanh::LeanObject,
    mut v_motive_6704_: *mut leanh::LeanObject,
    mut v_x_6705_: *mut leanh::LeanObject,
    mut v_x_6706_: *mut leanh::LeanObject,
    mut v_h__1_6707_: *mut leanh::LeanObject,
    mut v_h__2_6708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6710_: u8 = 0;
    v_zero_6709_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6710_ = lean_nat_dec_eq(v_x_6705_, v_zero_6709_);
    if v_isZero_6710_ == 1 {
        let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6708_);
        v___x_6711_ = leanh::lean_apply_1(v_h__1_6707_, v_x_6706_);
        return v___x_6711_;
    } else {
        let mut v_one_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6707_);
        v_one_6712_ = leanh::lean_unsigned_to_nat(1);
        v_n_6713_ = lean_nat_sub(v_x_6705_, v_one_6712_);
        v___x_6714_ = leanh::lean_apply_2(v_h__2_6708_, v_n_6713_, v_x_6706_);
        return v___x_6714_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter___boxed(
    mut v_00_u03b1_6715_: *mut leanh::LeanObject,
    mut v_motive_6716_: *mut leanh::LeanObject,
    mut v_x_6717_: *mut leanh::LeanObject,
    mut v_x_6718_: *mut leanh::LeanObject,
    mut v_h__1_6719_: *mut leanh::LeanObject,
    mut v_h__2_6720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6721_ = l___private_Init_Data_List_Basic_0__List_replicateTR_loop_match__1_splitter(
        v_00_u03b1_6715_,
        v_motive_6716_,
        v_x_6717_,
        v_x_6718_,
        v_h__1_6719_,
        v_h__2_6720_,
    );
    leanh::lean_dec(v_x_6717_);
    return v_res_6721_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(
    mut v_x_6722_: *mut leanh::LeanObject,
    mut v_x_6723_: *mut leanh::LeanObject,
    mut v_h__1_6724_: *mut leanh::LeanObject,
    mut v_h__2_6725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6727_: u8 = 0;
    v_zero_6726_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6727_ = lean_nat_dec_eq(v_x_6722_, v_zero_6726_);
    if v_isZero_6727_ == 1 {
        let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6725_);
        v___x_6728_ = leanh::lean_apply_1(v_h__1_6724_, v_x_6723_);
        return v___x_6728_;
    } else {
        let mut v_one_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6724_);
        v_one_6729_ = leanh::lean_unsigned_to_nat(1);
        v_n_6730_ = lean_nat_sub(v_x_6722_, v_one_6729_);
        v___x_6731_ = leanh::lean_apply_2(v_h__2_6725_, v_n_6730_, v_x_6723_);
        return v___x_6731_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg___boxed(
    mut v_x_6732_: *mut leanh::LeanObject,
    mut v_x_6733_: *mut leanh::LeanObject,
    mut v_h__1_6734_: *mut leanh::LeanObject,
    mut v_h__2_6735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6736_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___redArg(
        v_x_6732_,
        v_x_6733_,
        v_h__1_6734_,
        v_h__2_6735_,
    );
    leanh::lean_dec(v_x_6732_);
    return v_res_6736_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(
    mut v_00_u03b1_6737_: *mut leanh::LeanObject,
    mut v_motive_6738_: *mut leanh::LeanObject,
    mut v_x_6739_: *mut leanh::LeanObject,
    mut v_x_6740_: *mut leanh::LeanObject,
    mut v_h__1_6741_: *mut leanh::LeanObject,
    mut v_h__2_6742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6744_: u8 = 0;
    v_zero_6743_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6744_ = lean_nat_dec_eq(v_x_6739_, v_zero_6743_);
    if v_isZero_6744_ == 1 {
        let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6742_);
        v___x_6745_ = leanh::lean_apply_1(v_h__1_6741_, v_x_6740_);
        return v___x_6745_;
    } else {
        let mut v_one_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6741_);
        v_one_6746_ = leanh::lean_unsigned_to_nat(1);
        v_n_6747_ = lean_nat_sub(v_x_6739_, v_one_6746_);
        v___x_6748_ = leanh::lean_apply_2(v_h__2_6742_, v_n_6747_, v_x_6740_);
        return v___x_6748_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter___boxed(
    mut v_00_u03b1_6749_: *mut leanh::LeanObject,
    mut v_motive_6750_: *mut leanh::LeanObject,
    mut v_x_6751_: *mut leanh::LeanObject,
    mut v_x_6752_: *mut leanh::LeanObject,
    mut v_h__1_6753_: *mut leanh::LeanObject,
    mut v_h__2_6754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6755_ = l___private_Init_Data_List_Basic_0__List_replicate_match__1_splitter(
        v_00_u03b1_6749_,
        v_motive_6750_,
        v_x_6751_,
        v_x_6752_,
        v_h__1_6753_,
        v_h__2_6754_,
    );
    leanh::lean_dec(v_x_6751_);
    return v_res_6755_;
}
pub unsafe fn l_List_leftpadTR___redArg(
    mut v_n_6756_: *mut leanh::LeanObject,
    mut v_a_6757_: *mut leanh::LeanObject,
    mut v_l_6758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6759_ = l_List_lengthTR___redArg(v_l_6758_);
    v___x_6760_ = lean_nat_sub(v_n_6756_, v___x_6759_);
    leanh::lean_dec(v___x_6759_);
    v___x_6761_ = l_List_replicateTR_loop___redArg(v_a_6757_, v___x_6760_, v_l_6758_);
    return v___x_6761_;
}
pub unsafe fn l_List_leftpadTR___redArg___boxed(
    mut v_n_6762_: *mut leanh::LeanObject,
    mut v_a_6763_: *mut leanh::LeanObject,
    mut v_l_6764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6765_ = l_List_leftpadTR___redArg(v_n_6762_, v_a_6763_, v_l_6764_);
    leanh::lean_dec(v_n_6762_);
    return v_res_6765_;
}
pub unsafe fn l_List_leftpadTR(
    mut v_00_u03b1_6766_: *mut leanh::LeanObject,
    mut v_n_6767_: *mut leanh::LeanObject,
    mut v_a_6768_: *mut leanh::LeanObject,
    mut v_l_6769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6770_ = l_List_lengthTR___redArg(v_l_6769_);
    v___x_6771_ = lean_nat_sub(v_n_6767_, v___x_6770_);
    leanh::lean_dec(v___x_6770_);
    v___x_6772_ = l_List_replicateTR_loop___redArg(v_a_6768_, v___x_6771_, v_l_6769_);
    return v___x_6772_;
}
pub unsafe fn l_List_leftpadTR___boxed(
    mut v_00_u03b1_6773_: *mut leanh::LeanObject,
    mut v_n_6774_: *mut leanh::LeanObject,
    mut v_a_6775_: *mut leanh::LeanObject,
    mut v_l_6776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6777_ = l_List_leftpadTR(v_00_u03b1_6773_, v_n_6774_, v_a_6775_, v_l_6776_);
    leanh::lean_dec(v_n_6774_);
    return v_res_6777_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0___redArg(
    mut v_init_6778_: *mut leanh::LeanObject,
    mut v_x_6779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6784_: u8 = 0;
    let mut v_fst_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6789_: u8 = 0;
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6795_: u8 = 0;
    let mut v___x_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6805_: u8 = 0;
    let mut v_isSharedCheck_6806_: u8 = 0;
    let mut v_isSharedCheck_6807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6779_) == 0 {
                    leanh::lean_inc_ref(v_init_6778_);
                    return v_init_6778_;
                } else {
                    v_head_6780_ = leanh::lean_ctor_get(v_x_6779_, 0);
                    v_tail_6781_ = leanh::lean_ctor_get(v_x_6779_, 1);
                    v_isSharedCheck_6807_ = (!leanh::lean_is_exclusive(v_x_6779_)) as u8;
                    if v_isSharedCheck_6807_ == 0 {
                        v___x_6783_ = v_x_6779_;
                        v_isShared_6784_ = v_isSharedCheck_6807_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6781_);
                        leanh::lean_inc(v_head_6780_);
                        leanh::lean_dec(v_x_6779_);
                        v___x_6783_ = leanh::lean_box(0);
                        v_isShared_6784_ = v_isSharedCheck_6807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6785_ = leanh::lean_ctor_get(v_head_6780_, 0);
                v_snd_6786_ = leanh::lean_ctor_get(v_head_6780_, 1);
                v_isSharedCheck_6806_ = (!leanh::lean_is_exclusive(v_head_6780_)) as u8;
                if v_isSharedCheck_6806_ == 0 {
                    v___x_6788_ = v_head_6780_;
                    v_isShared_6789_ = v_isSharedCheck_6806_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6786_);
                    leanh::lean_inc(v_fst_6785_);
                    leanh::lean_dec(v_head_6780_);
                    v___x_6788_ = leanh::lean_box(0);
                    v_isShared_6789_ = v_isSharedCheck_6806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6790_ =
                    l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6778_, v_tail_6781_);
                v_fst_6791_ = leanh::lean_ctor_get(v___x_6790_, 0);
                v_snd_6792_ = leanh::lean_ctor_get(v___x_6790_, 1);
                v_isSharedCheck_6805_ = (!leanh::lean_is_exclusive(v___x_6790_)) as u8;
                if v_isSharedCheck_6805_ == 0 {
                    v___x_6794_ = v___x_6790_;
                    v_isShared_6795_ = v_isSharedCheck_6805_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6792_);
                    leanh::lean_inc(v_fst_6791_);
                    leanh::lean_dec(v___x_6790_);
                    v___x_6794_ = leanh::lean_box(0);
                    v_isShared_6795_ = v_isSharedCheck_6805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6784_ == 0 {
                    leanh::lean_ctor_set(v___x_6783_, 1, v_fst_6791_);
                    leanh::lean_ctor_set(v___x_6783_, 0, v_fst_6785_);
                    v___x_6797_ = v___x_6783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6804_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 0, v_fst_6785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6804_, 1, v_fst_6791_);
                    v___x_6797_ = v_reuseFailAlloc_6804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6789_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6788_, 1);
                    leanh::lean_ctor_set(v___x_6788_, 1, v_snd_6792_);
                    leanh::lean_ctor_set(v___x_6788_, 0, v_snd_6786_);
                    v___x_6799_ = v___x_6788_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6803_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_snd_6786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 1, v_snd_6792_);
                    v___x_6799_ = v_reuseFailAlloc_6803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6795_ == 0 {
                    leanh::lean_ctor_set(v___x_6794_, 1, v___x_6799_);
                    leanh::lean_ctor_set(v___x_6794_, 0, v___x_6797_);
                    v___x_6801_ = v___x_6794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 0, v___x_6797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6802_, 1, v___x_6799_);
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
    mut v_init_6808_: *mut leanh::LeanObject,
    mut v_x_6809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6810_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6808_, v_x_6809_);
    leanh::lean_dec_ref(v_init_6808_);
    return v_res_6810_;
}
pub unsafe fn l_List_unzipTR___redArg(
    mut v_l_6811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6812_ = l_List_partition___redArg___closed__0;
    v___x_6813_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v___x_6812_, v_l_6811_);
    return v___x_6813_;
}
pub unsafe fn l_List_unzipTR(
    mut v_00_u03b1_6814_: *mut leanh::LeanObject,
    mut v_00_u03b2_6815_: *mut leanh::LeanObject,
    mut v_l_6816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6817_ = l_List_unzipTR___redArg(v_l_6816_);
    return v___x_6817_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0(
    mut v_00_u03b1_6818_: *mut leanh::LeanObject,
    mut v_00_u03b2_6819_: *mut leanh::LeanObject,
    mut v_init_6820_: *mut leanh::LeanObject,
    mut v_x_6821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6822_ = l_List_foldr___at___00List_unzipTR_spec__0___redArg(v_init_6820_, v_x_6821_);
    return v___x_6822_;
}
pub unsafe fn l_List_foldr___at___00List_unzipTR_spec__0___boxed(
    mut v_00_u03b1_6823_: *mut leanh::LeanObject,
    mut v_00_u03b2_6824_: *mut leanh::LeanObject,
    mut v_init_6825_: *mut leanh::LeanObject,
    mut v_x_6826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6827_ = l_List_foldr___at___00List_unzipTR_spec__0(
        v_00_u03b1_6823_,
        v_00_u03b2_6824_,
        v_init_6825_,
        v_x_6826_,
    );
    leanh::lean_dec_ref(v_init_6825_);
    return v_res_6827_;
}
pub unsafe fn l_List_range_x27TR_go(
    mut v_step_6828_: *mut leanh::LeanObject,
    mut v_a_6829_: *mut leanh::LeanObject,
    mut v_a_6830_: *mut leanh::LeanObject,
    mut v_a_6831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6833_: u8 = 0;
    let mut v_one_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6832_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_6833_ = lean_nat_dec_eq(v_a_6829_, v_zero_6832_);
                if v_isZero_6833_ == 1 {
                    leanh::lean_dec(v_a_6830_);
                    leanh::lean_dec(v_a_6829_);
                    return v_a_6831_;
                } else {
                    v_one_6834_ = leanh::lean_unsigned_to_nat(1);
                    v_n_6835_ = lean_nat_sub(v_a_6829_, v_one_6834_);
                    leanh::lean_dec(v_a_6829_);
                    v___x_6836_ = lean_nat_sub(v_a_6830_, v_step_6828_);
                    leanh::lean_dec(v_a_6830_);
                    leanh::lean_inc(v___x_6836_);
                    v___x_6837_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6837_, 0, v___x_6836_);
                    leanh::lean_ctor_set(v___x_6837_, 1, v_a_6831_);
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
    mut v_step_6839_: *mut leanh::LeanObject,
    mut v_a_6840_: *mut leanh::LeanObject,
    mut v_a_6841_: *mut leanh::LeanObject,
    mut v_a_6842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6843_ = l_List_range_x27TR_go(v_step_6839_, v_a_6840_, v_a_6841_, v_a_6842_);
    leanh::lean_dec(v_step_6839_);
    return v_res_6843_;
}
pub unsafe fn l_List_range_x27TR(
    mut v_s_6844_: *mut leanh::LeanObject,
    mut v_n_6845_: *mut leanh::LeanObject,
    mut v_step_6846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6847_ = lean_nat_mul(v_step_6846_, v_n_6845_);
    v___x_6848_ = lean_nat_add(v_s_6844_, v___x_6847_);
    leanh::lean_dec(v___x_6847_);
    v___x_6849_ = leanh::lean_box(0);
    v___x_6850_ = l_List_range_x27TR_go(v_step_6846_, v_n_6845_, v___x_6848_, v___x_6849_);
    return v___x_6850_;
}
pub unsafe fn l_List_range_x27TR___boxed(
    mut v_s_6851_: *mut leanh::LeanObject,
    mut v_n_6852_: *mut leanh::LeanObject,
    mut v_step_6853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6854_ = l_List_range_x27TR(v_s_6851_, v_n_6852_, v_step_6853_);
    leanh::lean_dec(v_step_6853_);
    leanh::lean_dec(v_s_6851_);
    return v_res_6854_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(
    mut v_x_6855_: *mut leanh::LeanObject,
    mut v_x_6856_: *mut leanh::LeanObject,
    mut v_x_6857_: *mut leanh::LeanObject,
    mut v_h__1_6858_: *mut leanh::LeanObject,
    mut v_h__2_6859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6861_: u8 = 0;
    v_zero_6860_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6861_ = lean_nat_dec_eq(v_x_6855_, v_zero_6860_);
    if v_isZero_6861_ == 1 {
        let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6859_);
        v___x_6862_ = leanh::lean_apply_2(v_h__1_6858_, v_x_6856_, v_x_6857_);
        return v___x_6862_;
    } else {
        let mut v_one_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6858_);
        v_one_6863_ = leanh::lean_unsigned_to_nat(1);
        v_n_6864_ = lean_nat_sub(v_x_6855_, v_one_6863_);
        v___x_6865_ = leanh::lean_apply_3(v_h__2_6859_, v_n_6864_, v_x_6856_, v_x_6857_);
        return v___x_6865_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg___boxed(
    mut v_x_6866_: *mut leanh::LeanObject,
    mut v_x_6867_: *mut leanh::LeanObject,
    mut v_x_6868_: *mut leanh::LeanObject,
    mut v_h__1_6869_: *mut leanh::LeanObject,
    mut v_h__2_6870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6871_ =
        l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___redArg(
            v_x_6866_,
            v_x_6867_,
            v_x_6868_,
            v_h__1_6869_,
            v_h__2_6870_,
        );
    leanh::lean_dec(v_x_6866_);
    return v_res_6871_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(
    mut v_motive_6872_: *mut leanh::LeanObject,
    mut v_x_6873_: *mut leanh::LeanObject,
    mut v_x_6874_: *mut leanh::LeanObject,
    mut v_x_6875_: *mut leanh::LeanObject,
    mut v_h__1_6876_: *mut leanh::LeanObject,
    mut v_h__2_6877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_6879_: u8 = 0;
    v_zero_6878_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_6879_ = lean_nat_dec_eq(v_x_6873_, v_zero_6878_);
    if v_isZero_6879_ == 1 {
        let mut v___x_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_6877_);
        v___x_6880_ = leanh::lean_apply_2(v_h__1_6876_, v_x_6874_, v_x_6875_);
        return v___x_6880_;
    } else {
        let mut v_one_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6876_);
        v_one_6881_ = leanh::lean_unsigned_to_nat(1);
        v_n_6882_ = lean_nat_sub(v_x_6873_, v_one_6881_);
        v___x_6883_ = leanh::lean_apply_3(v_h__2_6877_, v_n_6882_, v_x_6874_, v_x_6875_);
        return v___x_6883_;
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter___boxed(
    mut v_motive_6884_: *mut leanh::LeanObject,
    mut v_x_6885_: *mut leanh::LeanObject,
    mut v_x_6886_: *mut leanh::LeanObject,
    mut v_x_6887_: *mut leanh::LeanObject,
    mut v_h__1_6888_: *mut leanh::LeanObject,
    mut v_h__2_6889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6890_ = l___private_Init_Data_List_Basic_0__List_range_x27TR_go_match__1_splitter(
        v_motive_6884_,
        v_x_6885_,
        v_x_6886_,
        v_x_6887_,
        v_h__1_6888_,
        v_h__2_6889_,
    );
    leanh::lean_dec(v_x_6885_);
    return v_res_6890_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
    mut v_sep_6891_: *mut leanh::LeanObject,
    mut v_init_6892_: *mut leanh::LeanObject,
    mut v_x_6893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6893_) == 0 {
                    leanh::lean_dec(v_sep_6891_);
                    leanh::lean_inc(v_init_6892_);
                    return v_init_6892_;
                } else {
                    v_head_6894_ = leanh::lean_ctor_get(v_x_6893_, 0);
                    v_tail_6895_ = leanh::lean_ctor_get(v_x_6893_, 1);
                    v_isSharedCheck_6904_ = (!leanh::lean_is_exclusive(v_x_6893_)) as u8;
                    if v_isSharedCheck_6904_ == 0 {
                        v___x_6897_ = v_x_6893_;
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6895_);
                        leanh::lean_inc(v_head_6894_);
                        leanh::lean_dec(v_x_6893_);
                        v___x_6897_ = leanh::lean_box(0);
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_sep_6891_);
                v___x_6899_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
                    v_sep_6891_,
                    v_init_6892_,
                    v_tail_6895_,
                );
                if v_isShared_6898_ == 0 {
                    leanh::lean_ctor_set(v___x_6897_, 1, v___x_6899_);
                    v___x_6901_ = v___x_6897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6903_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_head_6894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 1, v___x_6899_);
                    v___x_6901_ = v_reuseFailAlloc_6903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6902_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6902_, 0, v_sep_6891_);
                leanh::lean_ctor_set(v___x_6902_, 1, v___x_6901_);
                return v___x_6902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___redArg___boxed(
    mut v_sep_6905_: *mut leanh::LeanObject,
    mut v_init_6906_: *mut leanh::LeanObject,
    mut v_x_6907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6908_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
        v_sep_6905_,
        v_init_6906_,
        v_x_6907_,
    );
    leanh::lean_dec(v_init_6906_);
    return v_res_6908_;
}
pub unsafe fn l_List_intersperseTR___redArg(
    mut v_sep_6909_: *mut leanh::LeanObject,
    mut v_x_6910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6915_: u8 = 0;
    let mut v_head_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6930_: u8 = 0;
    let mut v_isSharedCheck_6931_: u8 = 0;
    let mut v_unused_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6910_) == 0 {
                    leanh::lean_dec(v_sep_6909_);
                    return v_x_6910_;
                } else {
                    v_tail_6911_ = leanh::lean_ctor_get(v_x_6910_, 1);
                    leanh::lean_inc(v_tail_6911_);
                    if leanh::lean_obj_tag(v_tail_6911_) == 0 {
                        leanh::lean_dec(v_sep_6909_);
                        return v_x_6910_;
                    } else {
                        v_head_6912_ = leanh::lean_ctor_get(v_x_6910_, 0);
                        v_isSharedCheck_6931_ = (!leanh::lean_is_exclusive(v_x_6910_)) as u8;
                        if v_isSharedCheck_6931_ == 0 {
                            v_unused_6932_ = leanh::lean_ctor_get(v_x_6910_, 1);
                            leanh::lean_dec(v_unused_6932_);
                            v___x_6914_ = v_x_6910_;
                            v_isShared_6915_ = v_isSharedCheck_6931_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_6912_);
                            leanh::lean_dec(v_x_6910_);
                            v___x_6914_ = leanh::lean_box(0);
                            v_isShared_6915_ = v_isSharedCheck_6931_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_head_6916_ = leanh::lean_ctor_get(v_tail_6911_, 0);
                v_tail_6917_ = leanh::lean_ctor_get(v_tail_6911_, 1);
                v_isSharedCheck_6930_ = (!leanh::lean_is_exclusive(v_tail_6911_)) as u8;
                if v_isSharedCheck_6930_ == 0 {
                    v___x_6919_ = v_tail_6911_;
                    v_isShared_6920_ = v_isSharedCheck_6930_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_6917_);
                    leanh::lean_inc(v_head_6916_);
                    leanh::lean_dec(v_tail_6911_);
                    v___x_6919_ = leanh::lean_box(0);
                    v_isShared_6920_ = v_isSharedCheck_6930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6921_ = leanh::lean_box(0);
                leanh::lean_inc(v_sep_6909_);
                v___x_6922_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
                    v_sep_6909_,
                    v___x_6921_,
                    v_tail_6917_,
                );
                if v_isShared_6920_ == 0 {
                    leanh::lean_ctor_set(v___x_6919_, 1, v___x_6922_);
                    v___x_6924_ = v___x_6919_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6929_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_head_6916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 1, v___x_6922_);
                    v___x_6924_ = v_reuseFailAlloc_6929_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6915_ == 0 {
                    leanh::lean_ctor_set(v___x_6914_, 1, v___x_6924_);
                    leanh::lean_ctor_set(v___x_6914_, 0, v_sep_6909_);
                    v___x_6926_ = v___x_6914_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6928_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_sep_6909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 1, v___x_6924_);
                    v___x_6926_ = v_reuseFailAlloc_6928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6927_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6927_, 0, v_head_6912_);
                leanh::lean_ctor_set(v___x_6927_, 1, v___x_6926_);
                return v___x_6927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_intersperseTR(
    mut v_00_u03b1_6933_: *mut leanh::LeanObject,
    mut v_sep_6934_: *mut leanh::LeanObject,
    mut v_x_6935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6936_ = l_List_intersperseTR___redArg(v_sep_6934_, v_x_6935_);
    return v___x_6936_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0(
    mut v_00_u03b1_6937_: *mut leanh::LeanObject,
    mut v_sep_6938_: *mut leanh::LeanObject,
    mut v_init_6939_: *mut leanh::LeanObject,
    mut v_x_6940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6941_ = l_List_foldr___at___00List_intersperseTR_spec__0___redArg(
        v_sep_6938_,
        v_init_6939_,
        v_x_6940_,
    );
    return v___x_6941_;
}
pub unsafe fn l_List_foldr___at___00List_intersperseTR_spec__0___boxed(
    mut v_00_u03b1_6942_: *mut leanh::LeanObject,
    mut v_sep_6943_: *mut leanh::LeanObject,
    mut v_init_6944_: *mut leanh::LeanObject,
    mut v_x_6945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6946_ = l_List_foldr___at___00List_intersperseTR_spec__0(
        v_00_u03b1_6942_,
        v_sep_6943_,
        v_init_6944_,
        v_x_6945_,
    );
    leanh::lean_dec(v_init_6944_);
    return v_res_6946_;
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter___redArg(
    mut v_x_6947_: *mut leanh::LeanObject,
    mut v_h__1_6948_: *mut leanh::LeanObject,
    mut v_h__2_6949_: *mut leanh::LeanObject,
    mut v_h__3_6950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6947_) == 0 {
        let mut v___x_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_6950_);
        leanh::lean_dec(v_h__2_6949_);
        v___x_6951_ = leanh::lean_box(0);
        v___x_6952_ = leanh::lean_apply_1(v_h__1_6948_, v___x_6951_);
        return v___x_6952_;
    } else {
        let mut v_tail_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6948_);
        v_tail_6953_ = leanh::lean_ctor_get(v_x_6947_, 1);
        if leanh::lean_obj_tag(v_tail_6953_) == 0 {
            let mut v_head_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_6950_);
            v_head_6954_ = leanh::lean_ctor_get(v_x_6947_, 0);
            leanh::lean_inc(v_head_6954_);
            leanh::lean_dec_ref_known(v_x_6947_, 2);
            v___x_6955_ = leanh::lean_apply_1(v_h__2_6949_, v_head_6954_);
            return v___x_6955_;
        } else {
            let mut v_head_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_6953_);
            leanh::lean_dec(v_h__2_6949_);
            v_head_6956_ = leanh::lean_ctor_get(v_x_6947_, 0);
            leanh::lean_inc(v_head_6956_);
            leanh::lean_dec_ref_known(v_x_6947_, 2);
            v_head_6957_ = leanh::lean_ctor_get(v_tail_6953_, 0);
            leanh::lean_inc(v_head_6957_);
            v_tail_6958_ = leanh::lean_ctor_get(v_tail_6953_, 1);
            leanh::lean_inc(v_tail_6958_);
            leanh::lean_dec_ref_known(v_tail_6953_, 2);
            v___x_6959_ =
                leanh::lean_apply_3(v_h__3_6950_, v_head_6956_, v_head_6957_, v_tail_6958_);
            return v___x_6959_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Basic_0__List_intersperseTR_match__1_splitter(
    mut v_00_u03b1_6960_: *mut leanh::LeanObject,
    mut v_motive_6961_: *mut leanh::LeanObject,
    mut v_x_6962_: *mut leanh::LeanObject,
    mut v_h__1_6963_: *mut leanh::LeanObject,
    mut v_h__2_6964_: *mut leanh::LeanObject,
    mut v_h__3_6965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6962_) == 0 {
        let mut v___x_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_6965_);
        leanh::lean_dec(v_h__2_6964_);
        v___x_6966_ = leanh::lean_box(0);
        v___x_6967_ = leanh::lean_apply_1(v_h__1_6963_, v___x_6966_);
        return v___x_6967_;
    } else {
        let mut v_tail_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_6963_);
        v_tail_6968_ = leanh::lean_ctor_get(v_x_6962_, 1);
        if leanh::lean_obj_tag(v_tail_6968_) == 0 {
            let mut v_head_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_6965_);
            v_head_6969_ = leanh::lean_ctor_get(v_x_6962_, 0);
            leanh::lean_inc(v_head_6969_);
            leanh::lean_dec_ref_known(v_x_6962_, 2);
            v___x_6970_ = leanh::lean_apply_1(v_h__2_6964_, v_head_6969_);
            return v___x_6970_;
        } else {
            let mut v_head_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_tail_6968_);
            leanh::lean_dec(v_h__2_6964_);
            v_head_6971_ = leanh::lean_ctor_get(v_x_6962_, 0);
            leanh::lean_inc(v_head_6971_);
            leanh::lean_dec_ref_known(v_x_6962_, 2);
            v_head_6972_ = leanh::lean_ctor_get(v_tail_6968_, 0);
            leanh::lean_inc(v_head_6972_);
            v_tail_6973_ = leanh::lean_ctor_get(v_tail_6968_, 1);
            leanh::lean_inc(v_tail_6973_);
            leanh::lean_dec_ref_known(v_tail_6968_, 2);
            v___x_6974_ =
                leanh::lean_apply_3(v_h__3_6965_, v_head_6971_, v_head_6972_, v_tail_6973_);
            return v___x_6974_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Zero(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_lex___auto__1 = _init_l_List_lex___auto__1();
    leanh::lean_mark_persistent(l_List_lex___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Zero(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Basic(builtin);
}